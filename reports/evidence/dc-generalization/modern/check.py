"""Run the existing exact-contract renderer on independently authored contracts."""
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
FORMAL = ROOT / "formalization"
spec = importlib.util.spec_from_file_location("thesis_verify", FORMAL / "scripts/verify.py")
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)
manifest = json.loads((HERE / "contracts.json").read_text())
manifest["public_root"] = "HiddenMonotonicity.ModernMonotoneDC"
driver = HERE / "Expected.lean"
driver.write_text(verify.exact_driver(manifest, HERE))
receipt = {"mode": "local-uncommitted-target-check", "commands": []}
for label, source in [("exact", driver), ("boundary", HERE / "Boundary.lean")]:
    cmd = ["lake", "env", "lean", str(source)]
    with (HERE / (label + ".log")).open("w") as log:
        result = subprocess.run(cmd, cwd=FORMAL, stdout=log, stderr=subprocess.STDOUT)
    (HERE / (label + ".exit")).write_text(str(result.returncode) + "\n")
    receipt["commands"].append({"command": cmd, "exit_code": result.returncode})
    (HERE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    if result.returncode:
        raise SystemExit(result.returncode)
