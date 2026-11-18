"""Audit native residual addition versus the current prepared DC path on CPU."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
CURRENT = ROOT / "code/playing_backward"
OFFICIAL = Path("/tmp/hidden-monotonicity-official-2026-11-16")
sys.path.insert(0, str(CURRENT))

import torch
from torch import nn
from bwgame import dc_decomposition
from bwgame.patcher import patch_model, unpatch_model, mark_output_layer
from bwgame.operations.base import init_catted, reconstruct_output, extract_sensitivities
from bwgame.operations.add import Add


class ResidualBlock(nn.Module):
    def __init__(self, conv):
        super().__init__()
        layer = (lambda: nn.Conv2d(4, 4, 3, padding=1)) if conv else (lambda: nn.Linear(4, 4))
        self.first, self.second = layer(), layer()
        self.relu = nn.ReLU()

    def forward(self, x):
        return x + self.second(self.relu(self.first(x)))


class ResidualNet(nn.Module):
    def __init__(self, conv):
        super().__init__()
        self.stem = nn.Conv2d(3, 4, 1) if conv else nn.Linear(3, 4)
        self.blocks = nn.Sequential(ResidualBlock(conv), ResidualBlock(conv))
        self.head = nn.Conv2d(4, 2, 1) if conv else nn.Linear(4, 2)

    def forward(self, x):
        return self.head(self.blocks(self.stem(x)))


def source_sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(conv, seed, prepared):
    torch.manual_seed(seed)
    model = ResidualNet(conv).double().eval()
    reference = copy.deepcopy(model)
    x = torch.randn((2, 3, 5, 5) if conv else (2, 3), dtype=torch.float64)
    original = x.clone().requires_grad_(True)
    output = reference(original)
    cotangent = torch.randn_like(output)
    (output * cotangent).sum().backward()
    pointers = {name: p.data_ptr() for name, p in model.named_parameters()}
    shapes = {name: list(p.shape) for name, p in model.named_parameters()}

    if prepared:
        with dc_decomposition(model, x, alpha=0.0, align_forward=False, align_backward=False) as dc:
            actual = dc.output
            (actual * cotangent).sum().backward()
            gradient = dc.reconstruct_gradient()
            packed_shape = list(dc.input_4.shape)
            patched_adds = sum(isinstance(m, Add) for m in model.modules())
    else:
        # Deliberately skip all FX preparation: original Python '+' stays native.
        patch_model(model)
        mark_output_layer(model.head)
        packed = init_catted(x)
        actual = reconstruct_output(model(packed))
        (actual * cotangent).sum().backward()
        gradient = extract_sensitivities(packed.grad).reconstruct_gradient()
        packed_shape = list(packed.shape)
        patched_adds = sum(isinstance(m, Add) for m in model.modules())
        unpatch_model(model)

    result = {
        "network": "two_residual_conv_blocks" if conv else "two_residual_mlp_blocks",
        "seed": seed,
        "path": "default_context_with_fx" if prepared else "module_patches_native_add",
        "input_shape": list(x.shape),
        "packed_input_shape": packed_shape,
        "custom_add_modules": patched_adds,
        "max_abs_output_error": float((actual.detach() - output.detach()).abs().max()),
        "max_abs_input_gradient_error": float((gradient - original.grad).abs().max()),
        "parameter_shapes_unchanged": shapes == {name: list(p.shape) for name, p in model.named_parameters()},
        "parameter_storage_unchanged": pointers == {name: p.data_ptr() for name, p in model.named_parameters()},
    }
    assert result["max_abs_output_error"] < 1e-12, result
    assert result["max_abs_input_gradient_error"] < 1e-12, result
    assert result["parameter_shapes_unchanged"] and result["parameter_storage_unchanged"], result
    assert patched_adds == (2 if prepared else 0), result
    return result


if __name__ == "__main__":
    torch.set_num_threads(2)
    results = [check(conv, seed, prepared)
               for conv in (False, True) for seed in (7, 19, 31) for prepared in (False, True)]
    report = {
        "status": "PASS",
        "torch": torch.__version__,
        "device": "cpu", "dtype": "float64", "alpha": 0,
        "reference_alignment": False,
        "official_download_path": str(OFFICIAL),
        "official_revision": subprocess.check_output(["git", "-C", str(OFFICIAL), "rev-parse", "HEAD"], text=True).strip(),
        "current_revision": subprocess.check_output(["git", "-C", str(CURRENT), "rev-parse", "HEAD"], text=True).strip(),
        "current_dirty_status": subprocess.check_output(["git", "-C", str(CURRENT), "status", "--porcelain"], text=True),
        "source_sha256": {str(p.relative_to(ROOT)): source_sha(p) for p in (
            CURRENT / "bwgame/operations/base.py", CURRENT / "bwgame/operations/add.py",
            CURRENT / "bwgame/operations/patch_builder.py", CURRENT / "bwgame/functional_replacer.py",
            CURRENT / "bwgame/dc_context.py", Path(__file__).resolve())},
        "cases": results,
        "limits": "Small deterministic residual MLPs/CNNs only, without alignment, attention, data-dependent normalization, or mixed-format constants. This checks residual packing and autograd accumulation, not all supported models or the convex Transformer formulas.",
    }
    destination = Path(__file__).with_name("residual-packing-check.json")
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "cases": len(results),
                     "max_output_error": max(r["max_abs_output_error"] for r in results),
                     "max_gradient_error": max(r["max_abs_input_gradient_error"] for r in results),
                     "report": str(destination)}, indent=2))
