#!/usr/bin/env python3
"""Render ten reproducible test-image comparisons from frozen ViT campaign caches.

Uses no GPU. Only ordinary Gradient is computed (once, on CPU); CAM and
SplitCAM maps are the exact maps already cached by the benchmark. Re-running
with an additional --split-campaign appends its available frozen selections.
The ten images remain fixed, independent of attribution values and metrics.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
SELECTION_RULE = "rank distinct target classes by sha256('vit-extension-classes-v1|' + class_id); take ten; within each take minimum sha256('vit-extension-images-v1|' + image_id)"


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def write_json(path, data):
    path = Path(path)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, indent=2) + "\n")
    tmp.replace(path)


def load_json(path):
    return json.loads(Path(path).read_text())


def selected_columns(campaign, expected_test, expected_checkpoint, pending):
    """Accept only frozen, validation-selected rows and complete test-map caches."""
    campaign = campaign.resolve()
    selection_path = campaign / "selected_frozen.json"
    if not selection_path.exists():
        pending.append({"campaign": str(campaign), "reason": "selection not frozen"})
        return []
    protocol_path = campaign / "protocol.json"
    protocol, selection = load_json(protocol_path), load_json(selection_path)
    if selection["protocol_sha256"] != sha(protocol_path):
        raise ValueError(f"Selection/protocol fingerprint mismatch: {campaign}")
    if protocol["test_manifest"] != expected_test or protocol["checkpoint"] != expected_checkpoint:
        raise ValueError(f"Different test population or checkpoint: {campaign}")
    columns = []
    for row in sorted(selection["rows"], key=lambda r: (r["method"], "loc" not in r["selected_by"])):
        cache = campaign / "test/.saliency_cache" / (row["row_label"] + ".npz")
        if not cache.exists():
            pending.append({"campaign": str(campaign), "row": row["row_label"], "reason": "test cache not ready"})
            continue
        params, method = row["params"], row["method"]
        roles = "/".join(row["selected_by"])
        if method in ("gcam", "lcam"):
            block = int(params["target_layer_name"].split("encoder_layer_")[1].split(".")[0]) + 1
            name = "Grad-CAM" if method == "gcam" else "LayerCAM"
            title = f"{name} ({roles})\nblock {block}"
            conditioning = "fully live original-model gradients"
        else:
            policy = params["policy"]
            conditioning = {"fixed_both": "fixed attention + LN", "fixed_ln": "fixed LN; live attention", "full": "live attention + LN"}[policy]
            formula = params["formula"].replace("_minus", "−").replace("_plus", "+")
            title = f"SplitCAM ({roles})\n{conditioning}\nb{params['block']}, α={params['alpha']:g}, {formula}"
            title += f", p={params.get('backward_scale_power', 1.0):g}"
        key = hashlib.sha256((str(campaign) + row["row_label"]).encode()).hexdigest()[:12]
        columns.append({"key": key, "title": title, "method": method, "conditioning": conditioning,
                        "params": params, "selected_by": row["selected_by"], "row_label": row["row_label"],
                        "campaign": str(campaign), "selection_sha256": sha(selection_path),
                        "protocol_sha256": sha(protocol_path), "cache": str(cache), "cache_sha256": sha(cache),
                        "postprocessing": protocol.get("postprocessing"), "precision": protocol.get("precision"),
                        "backward_scale_power_semantics": protocol.get("backward_scale_power_semantics"),
                        "stabilized_stream_scope": protocol.get("stabilized_stream_scope")})
    return columns


def gradient_maps(images, labels, ids, checkpoint, ptnb, out, threads):
    """Canonical signed channel-summed logit gradient on the unconditioned model."""
    import torch
    import torchvision
    from bwgame.evaluation.evaluator import Evaluator
    from bwgame.xai.methods.captum_methods import RawGradient
    torch.set_num_threads(threads)
    torch.set_num_interop_threads(1)
    sources = ["bwgame/evaluation/evaluator.py", "bwgame/composite_replacer.py",
               "bwgame/functional_replacer.py", "bwgame/xai/methods/captum_methods.py"]
    provenance = {"checkpoint": checkpoint, "source_sha256": {p: sha(ptnb / p) for p in sources},
                  "image_ids": ids.tolist(), "labels": labels.tolist(),
                  "input_sha256": hashlib.sha256(images.tobytes()).hexdigest(),
                  "semantics": "sum over RGB channels of derivative of annotated-class logit w.r.t. normalized input; no input multiplication, absolute value or clipping",
                  "preparation": "Evaluator.__init__: decomposed explicit attention, module replacement; no frozen attention or LayerNorm",
                  "device": "cpu", "dtype": "float32", "torch": torch.__version__, "torchvision": torchvision.__version__}
    cache, metadata = out / "gradient_cache.npz", out / "gradient_provenance.json"
    if cache.exists() and metadata.exists():
        stored = load_json(metadata)
        checksum = stored.pop("cache_sha256", None)
        if stored == provenance and checksum is not None:
            if sha(cache) != checksum:
                raise ValueError("Cached Gradient fingerprint mismatch")
            with np.load(cache, allow_pickle=False) as z:
                np.testing.assert_array_equal(z["image_ids"], ids)
                maps, predictions = z["maps"], z["predictions"]
                if maps.shape != (len(ids), 224, 224) or predictions.shape != (len(ids),) or not np.isfinite(maps).all():
                    raise ValueError("Invalid cached Gradient arrays")
                return maps, predictions, {**provenance, "cache_sha256": checksum}
    if sha(checkpoint["path"]) != checkpoint["sha256"]:
        raise ValueError("Checkpoint fingerprint mismatch")
    model = torchvision.models.vit_b_16(weights=None)
    model.load_state_dict(torch.load(checkpoint["path"], map_location="cpu", weights_only=True))
    model.eval()
    maps, predictions = [], []
    with tempfile.TemporaryDirectory(prefix="vit-extension-cpu-") as work:
        ev = Evaluator(model, [], torch.device("cpu"), Path(work), metric_configs=[],
                       save_heatmaps=False, cache_maps=False, batch_size=1, warmup=0)
        method = RawGradient(ev.model, torch.device("cpu"))
        method.channel_reduction = "sum"
        for image, label, image_id in zip(images, labels, ids):
            x = torch.from_numpy(image[None].copy()).float()
            ev.model.zero_grad(set_to_none=True)
            with torch.no_grad():
                predictions.append(int(ev.model(x).argmax(1)))
            a = method.attribute(x, torch.tensor([int(label)]))["input"][0]
            if not np.isfinite(a).all():
                raise ValueError(f"Non-finite Gradient: {image_id}")
            maps.append(a)
            print(f"CPU Gradient {len(maps)}/{len(ids)}: {image_id}", flush=True)
    maps, predictions = np.asarray(maps), np.asarray(predictions)
    np.savez_compressed(cache, maps=maps, predictions=predictions, image_ids=ids)
    provenance["cache_sha256"] = sha(cache)
    write_json(metadata, provenance)
    return maps, predictions, provenance


def render(args):
    os.environ["CUDA_VISIBLE_DEVICES"] = ""
    sys.path.insert(0, str(args.ptnb))
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_pdf import PdfPages
    from PIL import Image
    from torchvision.models import ViT_B_16_Weights
    from reproduce.qualitative_figure import render_mask, render_signed

    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    protocol = load_json(args.cam_campaign / "protocol.json")
    manifest, checkpoint = protocol["test_manifest"], protocol["checkpoint"]
    pending = []
    campaigns = [args.cam_campaign] + args.split_campaign
    columns = [c for p in campaigns for c in selected_columns(p, manifest, checkpoint, pending)]
    if not columns:
        raise ValueError("No frozen selected test maps available")
    # Exact data identity, not image-name matching alone, is verified below.
    with np.load(columns[0]["cache"], allow_pickle=False) as z:
        ids, labels = z["image_ids"], z["labels"]
        assert ids.tolist() == [m["image_name"] for m in manifest]
        classes = sorted(set(map(int, labels)), key=lambda y: hashlib.sha256(("vit-extension-classes-v1|" + str(y)).encode()).hexdigest())[:args.count]
        selected = [min(np.flatnonzero(labels == target).tolist(), key=lambda i: hashlib.sha256(("vit-extension-images-v1|" + str(ids[i])).encode()).hexdigest()) for target in classes]
        if len(selected) != args.count:
            raise ValueError("Not enough distinct target classes")
        choice = {"rule": SELECTION_RULE, "test_manifest_sha256": hashlib.sha256(json.dumps(manifest, sort_keys=True).encode()).hexdigest(),
                  "test_indices": selected, "image_ids": ids[selected].tolist(), "labels": labels[selected].tolist()}
        choice_path = out / "selection.json"
        if choice_path.exists() and load_json(choice_path) != choice:
            raise ValueError("Candidate image selection changed; use a different output directory")
        write_json(choice_path, choice)
        images, masks = z["images"][selected], z["masks"][selected]
    all_maps = []
    for column in columns:
        with np.load(column["cache"], allow_pickle=False) as z:
            np.testing.assert_array_equal(z["image_ids"], ids)
            np.testing.assert_array_equal(z["labels"], labels)
            np.testing.assert_array_equal(z["images"][selected], images)
            np.testing.assert_array_equal(z["masks"][selected], masks)
            a = z["map__input"][selected]
            if a.shape != (args.count, 224, 224) or not np.isfinite(a).all():
                raise ValueError(f"Incomplete or invalid selected cache: {column['cache']}")
            all_maps.append(a)
    gradient, predictions, gradient_provenance = gradient_maps(images, labels[selected], ids[selected], checkpoint, args.ptnb, out, args.threads)
    columns.insert(0, {"key": "gradient", "title": "Gradient\noriginal model", "method": "gradient", "params": {"channel_reduction": "sum"},
                       "selected_by": ["fixed"], "conditioning": "fully live original-model gradients", "provenance": "gradient_provenance.json"})
    all_maps.insert(0, gradient)
    categories = ViT_B_16_Weights.IMAGENET1K_V1.meta["categories"]
    names = [categories[int(label)] for label in labels[selected]]
    ncols = len(columns) + 2
    tiles, entries = [], []
    for n, (i, image, mask, name) in enumerate(zip(selected, images, masks, names), 1):
        folder = out / f"{n:02d}_{Path(str(ids[i])).stem}"
        folder.mkdir(exist_ok=True)
        rgb = np.moveaxis(image * np.asarray([.229, .224, .225], dtype=np.float32)[:, None, None] + np.asarray([.485, .456, .406], dtype=np.float32)[:, None, None], 0, -1)
        row = [(np.clip(rgb, 0, 1) * 255).astype(np.uint8), render_mask(mask)]
        row.extend(render_signed(m[n-1]) for m in all_maps)
        files = ["original", "mask"] + [c["key"] for c in columns]
        for filename, tile in zip(files, row):
            Image.fromarray(tile).save(folder / (filename + ".png"))
        np.savez_compressed(folder / "raw_maps.npz", **{c["key"]: m[n-1] for c, m in zip(columns, all_maps)})
        entry = {"candidate": n, "test_index": i, "image_id": str(ids[i]), "target": int(labels[i]), "target_class": name,
                 "prediction": int(predictions[n-1]), "prediction_class": categories[int(predictions[n-1])],
                 "correctly_classified": bool(predictions[n-1] == labels[i]), "source": manifest[i], "folder": str(folder),
                 "maps": {c["key"]: {"min": float(m[n-1].min()), "max": float(m[n-1].max()),
                          "raw_array_sha256": hashlib.sha256(m[n-1].tobytes()).hexdigest()} for c, m in zip(columns, all_maps)}}
        tiles.append(row); entries.append(entry)
    headers = ["Input", "Object mask"] + [c["title"] for c in columns]
    footer = "Annotated class target in every column. Red: positive; blue: negative. Each sign uses its image-wide 99th percentile (maximum if zero), then clipping.\nLoc/faith denote validation-only selection; black is zero. Display scaling is independent of the quantitative evaluation."
    with PdfPages(out / "candidates.pdf") as pdf:
        for row, entry in zip(tiles, entries):
            fig, axes = plt.subplots(1, ncols, figsize=(2.35*ncols, 3.7))
            for ax, tile, header in zip(axes, row, headers):
                ax.imshow(tile, interpolation="nearest"); ax.set_title(header, fontsize=10); ax.axis("off")
            title = f"{entry['candidate']:02d} · {entry['target_class']} · {entry['image_id']}"
            title += f"  |  top-1: {entry['prediction_class']}"
            fig.suptitle(title, fontsize=13, y=.985)
            fig.text(.5, .045, footer, ha="center", fontsize=8)
            fig.subplots_adjust(left=.012, right=.988, top=.77, bottom=.19, wspace=.08)
            path = out / (f"candidate_{entry['candidate']:02d}.png")
            fig.savefig(path, dpi=170, facecolor="white")
            pdf.savefig(fig, facecolor="white"); plt.close(fig)
            entry["panel"] = str(path)
            entry["panel_sha256"] = sha(path)
    fig, axes = plt.subplots(args.count, ncols, figsize=(2*ncols, 2.42*args.count), squeeze=False)
    for r, (row, entry) in enumerate(zip(tiles, entries)):
        for c, (ax, tile) in enumerate(zip(axes[r], row)):
            ax.imshow(tile, interpolation="nearest"); ax.axis("off")
            if r == 0:
                ax.set_title(headers[c], fontsize=9)
        axes[r, 0].text(0, -.07, f"{r+1:02d} {entry['target_class']}\n{Path(entry['image_id']).stem.replace('ILSVRC2012_val_', '')}", transform=axes[r, 0].transAxes, fontsize=9, va="top")
    fig.suptitle("ViT extension: ten held-out qualitative candidates", fontsize=16, y=.997)
    fig.text(.5, .006, footer, ha="center", fontsize=8)
    fig.subplots_adjust(left=.015, right=.99, top=.96, bottom=.035, hspace=.21, wspace=.07)
    fig.savefig(out / "contact_sheet.png", dpi=160, facecolor="white")
    fig.savefig(out / "contact_sheet.pdf", facecolor="white"); plt.close(fig)
    # Deliberately a candidate artifact, never an automatically included thesis page.
    tex_headers = [header.replace("α", r"\(\alpha\)").replace("−", r"\(-\)").replace("_", r"\_") for header in headers]
    tex = ["% Candidate rows only; choose examples before inclusion in the thesis.", r"\begingroup\setlength{\tabcolsep}{0pt}\scriptsize", "\\begin{tabular}{" + "c" * ncols + "}"]
    tex.append(" & ".join(r"\shortstack{" + header.replace("\n", r"\\") + "}" for header in tex_headers) + r" \\")
    for entry in entries:
        files = ["original", "mask"] + [c["key"] for c in columns]
        tex.append(" & ".join(r"\includegraphics[width=" + f"{.97/ncols:.4f}" + r"\linewidth]{\detokenize{" + str(Path(entry["folder"]) / (name + ".png")) + "}}" for name in files) + r" \\")
    tex.append("\\end{tabular}\\endgroup")
    (out / "candidate_rows.tex").write_text("\n".join(tex) + "\n")
    result = {"status": "partial" if pending else "ready", "count": args.count, "method_columns": len(columns),
              "candidate_selection": choice, "columns": columns, "pending": pending, "examples": entries,
              "display": footer, "gradient": gradient_provenance, "script_sha256": sha(__file__),
              "reproduction": {"cwd": str(ROOT), "argv": [sys.executable, *sys.argv]},
              "render_source_sha256": sha(args.ptnb / "reproduce/qualitative_figure.py"),
              "validation": ["frozen selection protocol fingerprints", "identical checkpoint and test population", "identical cached IDs, target labels, selected normalized input tensors and masks", "finite 224x224 native maps", "ten distinct target classes selected without maps or metrics", "ordinary Gradient computed on CPU from canonical original model"],
              "artifacts": {name: {"path": str(out / name), "sha256": sha(out / name)} for name in ["contact_sheet.png", "contact_sheet.pdf", "candidates.pdf", "candidate_rows.tex"]}}
    write_json(out / "manifest.json", result)
    print(json.dumps({"status": result["status"], "count": args.count, "columns": len(columns), "out": str(out), "pending": pending}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cam-campaign", type=Path, required=True)
    parser.add_argument("--split-campaign", type=Path, action="append", default=[])
    parser.add_argument("--ptnb", type=Path, default=ROOT / "code/playing_backward")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--count", type=int, default=10)
    parser.add_argument("--threads", type=int, default=2)
    args = parser.parse_args()
    render(args)


if __name__ == "__main__":
    main()
