"""Publish a review receipt only after every recorded final check passes."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import subprocess

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[3]
MODULES = ["RoutingHistory", "RoutingPolicyBridge", "RoutingPolicyPaths",
           "RoutingHistorySteps", "RoutingObservations", "RoutingReadoutHistory"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    for stem in [*(name + "-source" for name in MODULES), "exact-types", "boundary"]:
        assert (OUT / (stem + ".exit")).read_text().strip() == "0", stem
        assert "error:" not in (OUT / (stem + ".log")).read_text(), stem
    hashes = json.loads((OUT / "source-sha256.json").read_text())
    assert all(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest
               for path, digest in hashes.items()), "Source closure changed during review"
    environment = json.loads((OUT / "environment.json").read_text())
    assert all(set(row["axioms"]) <= ALLOWED for row in environment)
    manifest = json.loads((OUT / "expected-types.json").read_text())
    expected = {target["declaration"] for target in manifest["targets"]}
    assert len(expected) == len(manifest["targets"])
    assert expected <= {row["declaration"] for row in environment}
    experiment = json.loads((OUT / "experiment-results.json").read_text())
    assert experiment["status"] == "passed"
    assert hashlib.sha256((OUT / "experiment-cases.json").read_bytes()).hexdigest() == experiment["case_sha256"]
    details = json.loads((OUT / "source-correspondence.json").read_text())
    details["status"] = "pass_with_explicit_scope"
    details["pending"] = []
    details["validation"] = {
        "mode": "independent_frozen_draft_review",
        "fresh_compiles": len(MODULES),
        "fresh_compile_results": {name: 0 for name in MODULES},
        "manually_authored_contracts": len(manifest["targets"]),
        "kernel_exact_type_module_universe_axiom_checks": "passed",
        "imported_project_theorem_axiom_closures": len(environment),
        "boundary_lean_consumer": "passed",
        "boundary_consumer_path": "reports/evidence/routing-bridge/review/Boundary.lean",
        "independent_exact_rational_experiment": experiment,
        "source_hashes": "reports/evidence/routing-bridge/review/source-sha256.json",
        "sources_unchanged": True,
        "production_edits": [],
        "shared_olean_writes": False,
    }
    details["completed_utc"] = datetime.now(timezone.utc).isoformat()
    (OUT / "source-correspondence.json").write_text(json.dumps(details, indent=2, ensure_ascii=False) + "\n")
    report = {
        "review_id": details["review_id"],
        "status": details["status"],
        "source_state": "Six frozen draft modules outside the public All import closure; this review is not a clean committed production-gate receipt.",
        "repository_head_at_review": subprocess.check_output(
            ["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip(),
        "high_severity_findings": [],
        "verified_counterexamples_to_claimed_theorems": [],
        "source_correspondence": "reports/evidence/routing-bridge/review/source-correspondence.json",
        "exact_contracts": "reports/evidence/routing-bridge/review/expected-types.json",
        "boundaries_to_preserve": details["boundaries_to_preserve"],
        "validation": details["validation"],
        "conclusion": "The frozen drafts faithfully connect actual canonical layered-game histories and first-step target marginals to the alpha-beta backward occupations, including genuine intermediate root observations and a forced ungated signed affine readout. No high-severity semantic or kernel defect found. Preserve the explicit scope; integrate and run the committed public gate before publishing upgraded links.",
        "completed_utc": details["completed_utc"],
    }
    target = ROOT / "reports/adversarial-routing-bridge-review.json"
    target.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    files = [target, *(p for p in OUT.rglob("*") if p.is_file()
                      and "__pycache__" not in p.parts and p.name != "evidence-sha256.json")]
    evidence = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                for path in sorted(files)}
    (OUT / "evidence-sha256.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(report["status"], len(manifest["targets"]), "contracts;",
          len(environment), "imported project theorem axiom closures")


if __name__ == "__main__":
    main()
