#!/usr/bin/env python3
"""Render independent contracts using the established exact-type driver, then check them."""
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import shutil

BASE = Path(__file__).resolve().parent
OUT = BASE / sys.argv[1] if len(sys.argv) > 1 else BASE
ROOT = BASE.parents[3]
FORMAL = ROOT / "formalization"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((OUT / "contracts.json").read_text())
    spec = importlib.util.spec_from_file_location("reviewed_driver", FORMAL / "scripts/verify.py")
    driver = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(driver)
    closure = driver.import_closure(manifest["public_root"])
    sources = {m: sha(driver.local_module(m)) for m in closure}
    rendered = OUT / "ExactTypes.lean"
    pending = OUT / "ExactTypes.lean.pending"
    pending.write_text(driver.exact_driver(manifest, OUT), encoding="utf-8")
    pending.replace(rendered)
    receipt = {
        "mode": "isolated_diagnostic_independent_review",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "public_root": manifest["public_root"],
        "exact_contract_count": len(manifest["targets"]),
        "source_sha256": sources,
        "commands": [],
        "status": "running",
    }
    checks = [("exact", rendered), ("boundary", OUT / "BoundaryConsumers.lean")]
    if "--boundary-only" in sys.argv:
        previous = json.loads((OUT / "receipt.json").read_text())
        assert previous["source_sha256"] == sources, "Source changed since exact audit"
        assert previous["commands"][0]["exit_code"] == 0, "No successful exact audit to reuse"
        for path in [OUT / "contracts.json", rendered, OUT / "environment.json"]:
            assert previous["artifacts"][path.name] == sha(path), "Exact inputs changed"
        for name in ["boundary.log", "boundary.exit", "receipt.json"]:
            shutil.copy2(OUT / name, OUT / ("attempt-1-" + name))
        receipt["commands"] = previous["commands"][:1]
        receipt["reused_exact_audit_completed_utc"] = previous["completed_utc"]
        checks = checks[1:]
    for label, source in checks:
        log = OUT / (label + ".log")
        command = ["lake", "env", "lean", str(source)]
        with log.open("w") as stream:
            result = subprocess.run(command, cwd=FORMAL, stdout=stream, stderr=subprocess.STDOUT)
        (OUT / (label + ".exit")).write_text(str(result.returncode) + "\n")
        receipt["commands"].append({"command": command, "exit_code": result.returncode,
                                   "log": log.name, "sha256": sha(log)})
    environment = json.loads((OUT / "environment.json").read_text())
    bad = [r for r in environment if set(r["axioms"]) - set(manifest["allowed_axioms"])]
    receipt["environment_theorem_count"] = len(environment)
    receipt["unapproved_axioms"] = bad
    receipt["source_stable"] = sources == {m: sha(driver.local_module(m)) for m in closure}
    receipt["status"] = "passed" if (all(c["exit_code"] == 0 for c in receipt["commands"])
                                      and not bad and receipt["source_stable"]) else "failed"
    receipt["completed_utc"] = datetime.now(timezone.utc).isoformat()
    receipt["artifacts"] = {p.name: sha(p) for p in [OUT / "contracts.json", rendered,
                                                    OUT / "BoundaryConsumers.lean", OUT / "environment.json"]}
    (OUT / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: receipt[k] for k in ["status", "exact_contract_count", "environment_theorem_count", "source_stable"]}))
    raise SystemExit(0 if receipt["status"] == "passed" else 1)


if __name__ == "__main__":
    main()
