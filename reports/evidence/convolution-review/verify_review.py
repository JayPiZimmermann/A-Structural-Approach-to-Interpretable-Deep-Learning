#!/usr/bin/env python3
"""Reproduce the independent ConvexInput/Convolution review checks.

The seven contract texts were reviewed against the definitions and source scope;
this script checks those fixed statements using the repository's direct kernel
type/universe/module/axiom checker. It does not infer intended statements from
Lean declarations. Source builds are sequential and do not replace .olean files.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
FORMAL = ROOT / "formalization"
SOURCES = ["HiddenMonotonicity/ConvexInput.lean", "HiddenMonotonicity/Convolution.lean"]
CONTRACTS = ["convex-input-expected-types.json", "convolution-expected-types.json"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source_hashes = {"formalization/" + p: digest(FORMAL / p) for p in SOURCES}
    contract_hashes = {"reports/" + p: digest(ROOT / "reports" / p) for p in CONTRACTS}
    for p in SOURCES:
        (OUT / Path(p).name).write_bytes((FORMAL / p).read_bytes())
    targets = []
    for p in CONTRACTS:
        targets.extend(json.loads((ROOT / "reports" / p).read_text())["targets"])
    manifest = {"public_root": "HiddenMonotonicity.Convolution", "targets": targets}
    (OUT / "reviewed-types.json").write_text(json.dumps(manifest, indent=2) + "\n")
    spec = importlib.util.spec_from_file_location("project_verify", FORMAL / "scripts/verify.py")
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    driver = "import HiddenMonotonicity.ConvexInput\n" + verifier.exact_driver(manifest, OUT)
    (OUT / "ExactTypes.lean").write_text(driver)
    receipt = {"source_sha256": source_hashes, "contract_sha256": contract_hashes,
               "type_checker_sha256": digest(FORMAL / "scripts/verify.py"),
               "commands": [], "status": "running", "mode": "focused independent review"}
    def save():
        (OUT / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    save()
    commands = [("source-" + Path(p).stem, ["lake", "env", "lean", p]) for p in SOURCES]
    commands += [("exact-types", ["lake", "env", "lean", str(OUT / "ExactTypes.lean")]),
                 ("adversarial", ["lake", "env", "lean", str(OUT / "Adversarial.lean")])]
    for label, command in commands:
        print(label, flush=True)
        with (OUT / (label + ".log")).open("w") as stream:
            result = subprocess.run(command, cwd=FORMAL, stdout=stream, stderr=subprocess.STDOUT)
        (OUT / (label + ".exit")).write_text(str(result.returncode) + "\n")
        receipt["commands"].append({"name": label, "command": command, "cwd": "formalization",
                                     "exit_code": result.returncode,
                                     "log_sha256": digest(OUT / (label + ".log"))})
        save()
        if result.returncode:
            receipt["status"] = "failed"
            save()
            raise SystemExit(result.returncode)
    assert source_hashes == {"formalization/" + p: digest(FORMAL / p) for p in SOURCES}
    assert contract_hashes == {"reports/" + p: digest(ROOT / "reports" / p) for p in CONTRACTS}
    receipt["status"] = "passed"
    receipt["exact_target_count"] = len(targets)
    receipt["imported_project_theorem_count"] = len(json.loads((OUT / "environment.json").read_text()))
    receipt["adversarial_source_sha256"] = digest(OUT / "Adversarial.lean")
    save()


if __name__ == "__main__":
    main()
