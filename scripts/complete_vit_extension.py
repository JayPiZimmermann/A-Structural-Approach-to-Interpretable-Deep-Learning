#!/usr/bin/env python3
"""Stage completed ViT results, build an isolated thesis, then publish locally.

Default mode stages admitted results without editing TeX. --publish opts in to local
source/PDF updates; this script never commits, pushes, or starts GPU experiments.
"""
from __future__ import annotations

import argparse
import contextlib
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import math
from itertools import combinations
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
REPORT = Path("reports/vit-extension")
CHAPTER = Path("tex/chapters/08_experiments.tex")
ANCHOR = "% VIT_EXTENSION_INSERT_HERE"
BEGIN = "% BEGIN VIT_EXTENSION_GENERATED"
END = "% END VIT_EXTENSION_GENERATED"
INPUT = r"\input{tables/vit_extension/generated/integration}"
PREFIX = Path("tex/tables/vit_extension/generated")
STAGES = (("cam", "paper"), ("cam", "paper", "weaker"))
CAMPAIGNS = {
    "cam": ROOT.parent / "hidden-monotonicity-transformer-dc/results/vit_cam_paper_campaign/compact_2026-11-10",
    "paper": ROOT.parent / "hidden-monotonicity-transformer-dc/results/vit_paper_splitcam_campaign/compact_2026-11-10",
    "weaker": ROOT.parent / "hidden-monotonicity-live-stability/results/vit_paper_splitcam_campaign/weaker_2026-11-10",
}
PYTHON = ROOT.parent / "hidden-monotonicity-transformer-dc/.venv/bin/python"
AUX_SUFFIXES = {".aux", ".log", ".lof", ".lot", ".fls", ".out", ".toc", ".bcf",
                ".blg", ".bbl", ".idx", ".ilg", ".ind", ".nlo", ".nls", ".nlg",
                ".acn", ".acr", ".alg", ".glg", ".glo", ".gls", ".fdb_latexmk"}


def now():
    return datetime.now(timezone.utc).isoformat()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_hash(path):
    return digest(path.read_bytes()) if path.is_file() else None


def read_json(path, default=None):
    return json.loads(path.read_text()) if path.exists() else default


def atomic_bytes(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp-" + str(os.getpid()))
    with temporary.open("wb") as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)
    descriptor = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def write_json(path, value):
    atomic_bytes(path, (json.dumps(value, indent=2, sort_keys=True) + "\n").encode())


@contextlib.contextmanager
def lock(path, blocking=True):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a") as stream:
        fcntl.flock(stream, fcntl.LOCK_EX | (0 if blocking else fcntl.LOCK_NB))
        yield
        # Never unlink a flock file: another waiter may hold its original inode.


def safe_relative(value):
    path = Path(value)
    if path.is_absolute() or ".." in path.parts or not path.parts:
        raise ValueError("Unsafe artifact path: " + str(value))
    return path


def safe_target(root, name):
    relative = safe_relative(name)
    path = root
    for component in relative.parts:
        path = path / component
        if path.is_symlink():
            raise ValueError("Refusing a publication path containing a symlink: " + str(relative))
    return path


def managed_span(text):
    if BEGIN not in text and END not in text:
        return None
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        raise ValueError("Managed extension markers are missing or duplicated")
    first, last = text.index(BEGIN), text.index(END) + len(END)
    if last <= first:
        raise ValueError("Managed extension markers are reversed")
    return text[first:last]


def update_chapter(text, previous_span_hash):
    if text.count(ANCHOR) != 1:
        raise ValueError("Expected exactly one reserved extension anchor")
    desired = BEGIN + "\n" + INPUT + "\n" + END
    present = managed_span(text)
    if present is not None:
        if previous_span_hash is None or digest(present.encode()) != previous_span_hash:
            raise ValueError("Managed chapter span was edited; refusing to overwrite")
        return text.replace(present, desired), digest(desired.encode())
    if previous_span_hash is not None:
        raise ValueError("Previously published extension span was removed")
    return text.replace(ANCHOR, ANCHOR + "\n" + desired), digest(desired.encode())


def check_ownership(root, state):
    update_chapter((root / CHAPTER).read_text(), state.get("span_sha256"))
    for name, expected in state.get("managed_sha256", {}).items():
        path = safe_target(root, name)
        if file_hash(path) != expected:
            raise ValueError("Published extension file was edited: " + name)


def source_paths(root):
    paths = set()
    for directory in (root / "tex", root / "scripts"):
        for path in directory.rglob("*"):
            if not path.is_file() or "__pycache__" in path.parts:
                continue
            if path.suffix in AUX_SUFFIXES or path.name.endswith((".run.xml", ".synctex.gz")):
                continue
            if path.parent == root / "tex" and path.name in {"main.pdf", "supplement.pdf", "main.mw", "pdfa.xmpi"}:
                continue
            paths.add(path.relative_to(root))
    paths.update((Path("reports/evidence/page-budget/verify_publication.py"),
                  Path("reports/single-pdf/lean-alias-reviews.json"),
                  Path("reports/verification/current/receipt.json"),
                  Path("formalization/tex_links.json")))
    receipt = read_json(root / "reports/verification/current/receipt.json")
    paths.update(safe_relative(name) for name in receipt["source"]["sha256"])
    return sorted(paths)


def source_hashes(root):
    return {str(path): file_hash(root / path) for path in source_paths(root)}


def snapshot(root, destination):
    before = source_hashes(root)
    for name in before:
        source = root / name
        if source.is_symlink() and not source.is_file():
            raise ValueError("Broken source symlink: " + name)
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    copied = {name: file_hash(destination / name) for name in before}
    if copied != before or source_hashes(root) != before:
        raise ValueError("Sources changed while snapshotting; retry after edits settle")
    return before


def campaign_statuses():
    result = {}
    for name, path in CAMPAIGNS.items():
        try:
            result[name] = read_json(path / "status.json", {"stage": "missing"})
        except (OSError, ValueError) as error:
            result[name] = {"stage": "unreadable", "error": str(error)}
    return result


def eligible_stage(statuses):
    result = None
    for stage in STAGES:
        if all(statuses.get(name, {}).get("stage") in {"complete", "completed_no_admissible_configuration"} and
               not statuses[name].get("failures") for name in stage):
            result = stage
    return result


def campaign_stamp(names):
    # Include metadata/file changes after completion, without rereading multi-GB
    # native-map caches every minute. The adapter hashes the admitted sources.
    entries = []
    for name in names:
        for path in sorted(CAMPAIGNS[name].rglob("*")):
            if path.is_file() and path.suffix in {".json", ".csv", ".npz"}:
                stat = path.stat()
                entries.append((str(path), stat.st_size, stat.st_mtime_ns))
    for path in sorted((ROOT / "scripts").glob("*.py")):
        entries.append((str(path.relative_to(ROOT)), file_hash(path)))
    # External copied results and formatting/statistical code also affect the
    # table, even when the campaign status files themselves remain unchanged.
    for name in ("code/playing_backward/results_summary/test/vit_b16/gradient__cr-maxabs.json",
                 "code/playing_backward/results_summary/test/vit_b16/per_image_scores.csv.gz",
                 "code/playing_backward/results_summary/runtime/vit_b16.csv",
                 "tex/tables/ptnb_v2/generated/test_vit_b16_ci_longtable.tex",
                 "reports/vit-extension/gradient-provenance-review.json",
                 "reports/evidence/page-budget/verify_publication.py",
                 "code/playing_backward/reproduce/bootstrap_ci.py",
                 "code/playing_backward/reproduce/common.py",
                 "code/playing_backward/reproduce/qualitative_figure.py",
                 "code/playing_backward/bwgame/evaluation/stats.py",
                 "code/playing_backward/bwgame/evaluation/metric_spec.py"):
        entries.append((name, file_hash(ROOT / name)))
    return digest(json.dumps(entries, sort_keys=True).encode())


def run(command, cwd, log):
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open("a") as stream:
        stream.write("\n" + now() + " " + repr([str(x) for x in command]) + "\n")
        stream.flush()
        environment = dict(os.environ, CUDA_VISIBLE_DEVICES="", PYTHONDONTWRITEBYTECODE="1")
        return subprocess.run([str(x) for x in command], cwd=cwd, stdout=stream,
                              stderr=subprocess.STDOUT, env=environment, check=False).returncode


def validate_statistics(admission, output):
    summary = admission.get("combined_statistics", {})
    if summary.get("status") != "complete" or summary.get("path") != "combined_statistics.json":
        raise ValueError("Combined displayed-family statistics are incomplete")
    path = output / "combined_statistics.json"
    if path.is_symlink() or file_hash(path) != summary.get("sha256"):
        raise ValueError("Combined-statistics artifact hash mismatch")
    statistics = read_json(path)
    expected = ["gradient__cr-maxabs", *[row["row_label"] for row in admission["rows"]]]
    if (len(set(expected)) != len(expected) or summary.get("family_rows") != expected or
            statistics.get("family_rows") != expected or admission.get("n_rows") != len(expected)):
        raise ValueError("Combined-statistics family does not match every displayed configuration")
    metadata = statistics.get("metadata", {})
    if "rounded" not in metadata.get("historical_gradient", ""):
        raise ValueError("Copied Gradient precision limitation is not recorded")
    if set(statistics.get("metrics", {})) != {"AL", "PG", "TK", "PF5", "PF20", "Sel", "MaxS", "AvgS"}:
        raise ValueError("Combined statistics do not cover all eight metrics")
    expected_pairs = {frozenset(pair) for pair in combinations(expected, 2)}
    for metric, result in statistics["metrics"].items():
        pairs = result.get("pairs", [])
        if (set(result.get("rows", {})) != set(expected) or result.get("family_size") != len(expected_pairs) or
                len(pairs) != len(expected_pairs) or {frozenset((p["left"], p["right"])) for p in pairs} != expected_pairs):
            raise ValueError("Incomplete Holm family: " + metric)
        count = 200 if metric in {"MaxS", "AvgS"} else 565
        for row in result["rows"].values():
            if row.get("n") != count or not all(math.isfinite(row[key]) for key in ("mean", "lo", "hi")):
                raise ValueError("Invalid combined-statistics cell: " + metric)
        for pair in pairs:
            if pair.get("n") != count or not all(math.isfinite(pair[key]) and 0 <= pair[key] <= 1 for key in ("p", "p_holm")):
                raise ValueError("Invalid combined-statistics paired test: " + metric)
    return statistics


def audit_export(root, output, names, python):
    args = [python, root / "scripts/generate_vit_extension_table.py", "--out", output]
    for name in names:
        args.extend(("--campaign", name))
    code = run(args, root, output / "adapter.log")
    admission = read_json(output / "admission.json", {})
    if code != 0 or admission.get("ready") is not True:
        raise ValueError("Table admission incomplete; see " + str(output / "admission.json"))
    if tuple(admission.get("requested_campaigns", ())) != tuple(names):
        raise ValueError("Adapter admitted a different campaign set")
    if {c.get("name") for c in admission.get("campaigns", [])} != set(names) or any(
            c.get("ready") is not True or c.get("issues") for c in admission["campaigns"]):
        raise ValueError("Individual campaign admission is incomplete")
    if not any(row.get("campaign") in {"paper", "weaker"} or
               "splitcam" in str(row.get("label", "")).lower() for row in admission.get("rows", [])):
        raise ValueError("No valid SplitCAM row: a baseline-only extension is not publishable")
    for row in admission["rows"]:
        expected = {key: (200 if key in {"MaxS", "AvgS"} else 565)
                    for key in ("AL", "PG", "TK", "PF5", "PF20", "Sel", "MaxS", "AvgS")}
        if set(row.get("metrics", {})) != set(expected):
            raise ValueError("All eight quantitative metrics are required")
        for metric, count in expected.items():
            value = row["metrics"][metric]
            if (value.get("n") != count or value.get("coverage") != 1 or
                    not all(math.isfinite(value[k]) for k in ("mean", "lo", "hi")) or
                    not value["lo"] <= value["mean"] <= value["hi"]):
                raise ValueError("Incomplete quantitative cell: " + metric)
        runtime = row.get("runtime", {})
        if int(runtime.get("n_images", 0)) != 50 or int(runtime.get("failures", 1)) != 0:
            raise ValueError("Dedicated runtime measurement is incomplete")
    validate_statistics(admission, output)
    exports = {}
    for source_name, target_name in admission.get("exported_files", {}).items():
        source = output / safe_relative(source_name)
        target = Path("tex") / safe_relative(target_name)
        if not target.is_relative_to(PREFIX) or source.is_symlink() or not source.is_file():
            raise ValueError("Invalid adapter export: " + source_name)
        exports[str(target)] = source.read_bytes()
    if set(exports) != {str(PREFIX / name) for name in ("integration.tex", "extension_ci_longtable.tex")}:
        raise ValueError("Adapter export set changed; coordinator review required")
    return admission, exports


def render_candidates(root, output, names, python):
    args = [python, root / "scripts/render_vit_extension_candidates.py", "--cam-campaign", CAMPAIGNS["cam"],
            "--ptnb", root / "code/playing_backward", "--count", "10", "--threads", "2", "--out", output]
    for name in names:
        if name != "cam":
            args.extend(("--split-campaign", CAMPAIGNS[name]))
    if run(args, root, output / "render.log"):
        raise ValueError("Qualitative rendering failed; see " + str(output / "render.log"))
    manifest = read_json(output / "manifest.json", {})
    if manifest.get("status") != "ready" or manifest.get("count") != 10 or len(manifest.get("examples", [])) != 10:
        raise ValueError("Ten complete qualitative candidates are required")
    if not {"contact_sheet.png", "contact_sheet.pdf", "candidates.pdf", "candidate_rows.tex"} <= set(manifest.get("artifacts", {})):
        raise ValueError("Qualitative artifact manifest is incomplete")
    for number in range(1, 11):
        if not (output / f"candidate_{number:02d}.png").is_file():
            raise ValueError("Missing qualitative candidate")
    for name, info in manifest.get("artifacts", {}).items():
        artifact = output / safe_relative(name)
        if artifact.is_symlink() or file_hash(artifact) != info.get("sha256"):
            raise ValueError("Qualitative artifact hash mismatch: " + name)
    return manifest


def build_snapshot(stage):
    tex = stage / "tex"
    log = stage.parent / "build.log"
    latex = ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "main.tex"]
    for command in (latex, ["makeindex", "main.nlo", "-s", "nomencl.ist", "-o", "main.nls"], latex):
        if run(command, tex, log):
            raise ValueError("Isolated thesis build failed; see " + str(log))
    (stage / "docs").mkdir(exist_ok=True)
    shutil.copyfile(tex / "main.pdf", stage / "docs/thesis.pdf")
    guard = stage / "reports/evidence/page-budget/verify_publication.py"
    output = stage.parent / "publication-checks.json"
    if run([sys.executable, guard, "--output", output], stage, log):
        raise ValueError("Publication guard failed (warnings, references, proof links or 150-page cap); see " + str(output))
    checks = read_json(output)
    if checks.get("status") != "passed":
        raise ValueError("Publication guard did not explicitly pass")
    return checks


def extension_receipt(previous, checks, stage, release, admission, source_hash):
    """Keep prior editorial evidence explicitly historical, bind the new PDF."""
    receipt = json.loads(json.dumps(previous))
    artifact = checks["documents"]["thesis.pdf"]
    receipt.update({"built_at_utc": now(), "publication_mode": "single_pdf", "active_root": "tex/main.tex",
                    "publication_state": "single_pdf_built_and_checked_local_worktree",
                    "public_pdf": "docs/thesis.pdf", "pdf_sha256": artifact["sha256"],
                    "pages": artifact["pages"], "documents": checks["documents"], "checks": checks["checks"]})
    receipt["source_sha256"] = {name: file_hash(stage / name) for name in source_hash if name.startswith("tex/")}
    for path in (stage / PREFIX).glob("*.tex"):
        receipt["source_sha256"][str(path.relative_to(stage))] = file_hash(path)
    relative_release = str(release.relative_to(ROOT)) if release.is_relative_to(ROOT) else str(release)
    update = {"kind": "vit_extension", "updated_utc": now(), "release": relative_release,
              "prior_receipt": relative_release + "/previous-publication-build.json",
              "admission": relative_release + "/table/admission.json",
              "provenance": relative_release + "/table/provenance.json",
              "combined_statistics": relative_release + "/table/combined_statistics.json",
              "publication_guard": relative_release + "/publication-checks.json",
              "qualitative_candidates": relative_release + "/qualitative/manifest.json",
              "source_fingerprint": admission["source_fingerprint"],
              "authorization": "User requested local integration when the Quantus campaigns finish; root authorized the reviewed coordinator.",
              "summary": "Completed, validation-selected ViT extension results added to the main chapter; ten standalone qualitative candidates prepared for selection. No automatic git commit or push."}
    receipt.setdefault("extension_history", []).append(update)
    receipt["extension_update"] = update
    receipt["commands"] = ["Isolated snapshot: latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex",
                           "Isolated snapshot: makeindex main.nlo -s nomencl.ist -o main.nls",
                           "Isolated snapshot: repeat latexmk until references settle",
                           "Isolated snapshot: python3 reports/evidence/page-budget/verify_publication.py"]
    receipt["validation_scope"] = {
        "current": "Admitted campaign metrics and combined displayed-family statistics, ten qualitative candidate artifacts, isolated single-PDF build, warnings, internal destinations, pinned proof-source hashes and Lean URLs, source snapshot binding, and 150-page limit checked for this extension.",
        "historical": "Prior editorial, bibliography, content-retention and visual reviews are retained in the previous publication receipt; they are not claimed as fresh visual review of this extension PDF."}
    receipt["evidence_sha256"] = dict(previous.get("evidence_sha256", {}))
    for relative in ("table/admission.json", "table/provenance.json", "table/combined_statistics.json",
                     "qualitative/manifest.json", "publication-checks.json", "previous-publication-build.json"):
        receipt["evidence_sha256"][relative_release + "/" + relative] = file_hash(release / relative)
    return receipt


def recover_transaction(root, report):
    journal_path = report / "transaction.json"
    journal = read_json(journal_path)
    if not journal:
        return
    if journal.get("phase") == "committed":
        journal_path.unlink()
        return
    conflicts = []
    for entry in journal["files"]:
        actual = file_hash(safe_target(root, entry["path"]))
        if actual not in {entry["before"], entry["after"]}:
            conflicts.append(entry["path"])
    if conflicts:
        raise ValueError("Interrupted publication has subsequent edits; manual recovery needed: " + ", ".join(conflicts))
    for entry in journal["files"]:
        if entry["before"] is not None and file_hash(safe_target(report, entry["backup"])) != entry["before"]:
            raise ValueError("Publication rollback backup is missing/corrupt")
    for entry in reversed(journal["files"]):
        path = safe_target(root, entry["path"])
        if entry["before"] is None:
            path.unlink(missing_ok=True)
        else:
            backup = safe_target(report, entry["backup"])
            atomic_bytes(path, backup.read_bytes())
    journal_path.unlink()


def publish_transaction(root, report, replacements, fail_after=None):
    """Persist a crash-recoverable journal before replacing any live file."""
    recover_transaction(root, report)
    backup_dir = report / "rollback"
    backup_dir.mkdir(parents=True, exist_ok=True)
    entries = []
    for index, (name, data) in enumerate(replacements.items()):
        path = safe_target(root, name)
        backup = backup_dir / str(index)
        old = file_hash(path)
        if old is not None:
            atomic_bytes(backup, path.read_bytes())
        entries.append({"path": name, "before": old, "after": digest(data),
                        "backup": str(backup.relative_to(report))})
    journal = {"phase": "prepared", "started_utc": now(), "files": entries}
    write_json(report / "transaction.json", journal)
    try:
        for index, (name, data) in enumerate(replacements.items(), 1):
            path = safe_target(root, name)
            if file_hash(path) != entries[index - 1]["before"]:
                raise ValueError("Target changed during publication: " + name)
            atomic_bytes(path, data)
            if fail_after == index:
                raise RuntimeError("Injected publication failure")
        journal["phase"] = "committed"
        write_json(report / "transaction.json", journal)
        (report / "transaction.json").unlink()
    except BaseException:
        recover_transaction(root, report)
        raise


def process(root, report, names, python, publish, state, stamp):
    check_ownership(root, state)
    release = report / "releases" / (datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S") + "-" + stamp[:12])
    admission, exports = audit_export(root, release / "table", names, python)
    render_candidates(root, release / "qualitative", names, python)
    if not publish:
        return {"phase": "staged", "release": str(release), "admission": admission["source_fingerprint"]}
    stage = release / "snapshot"
    with lock(report / "tex-build.lock"):
        check_ownership(root, state)
        protected_names = ("docs/thesis.pdf", "reports/publication-build.json", "tex/main.pdf", "tex/main.log",
                           "tex/main.blg", str(REPORT / "state.json"), str(REPORT / "publication-checks.json"),
                           str(REPORT / "latest-artifacts.json"))
        protected_before = {name: file_hash(root / name) for name in protected_names}
        previous_receipt = read_json(root / "reports/publication-build.json", {})
        before = snapshot(root, stage)
    write_json(release / "previous-publication-build.json", previous_receipt)
    chapter, span_hash = update_chapter((stage / CHAPTER).read_text(), state.get("span_sha256"))
    replacements = dict(exports)
    replacements[str(CHAPTER)] = chapter.encode()
    for name, data in replacements.items():
        atomic_bytes(stage / name, data)
    checks = build_snapshot(stage)
    if campaign_stamp(names) != stamp:
        raise ValueError("Campaign artifacts changed during staging/build; retry")
    provenance = read_json(release / "table/provenance.json", {})
    if any(file_hash(Path(name)) != expected for name, expected in provenance.get("sources_sha256", {}).items()):
        raise ValueError("An admitted result/statistics source changed during the build; retry")
    new_state = {"schema": 1, "updated_utc": now(), "last_processed_input_hash": stamp,
                 "source_fingerprint": admission["source_fingerprint"], "campaigns": names,
                 "span_sha256": span_hash, "managed_sha256": {name: digest(data) for name, data in exports.items()},
                 "release": str(release), "pdf_sha256": file_hash(stage / "docs/thesis.pdf"),
                 "pages": checks["documents"]["thesis.pdf"]["pages"]}
    # The validated PDF is the last public artifact installed. State participates
    # in the same journal, so an interruption cannot mark a partial update done.
    replacements[str(REPORT / "publication-checks.json")] = (release / "publication-checks.json").read_bytes()
    replacements[str(REPORT / "state.json")] = (json.dumps(new_state, indent=2, sort_keys=True) + "\n").encode()
    artifact_names = ["contact_sheet.png", "candidates.pdf", "manifest.json", *[f"candidate_{i:02d}.png" for i in range(1, 11)]]
    latest = {"updated_utc": now(), "campaigns": names, "release": str(release),
              "source_fingerprint": admission["source_fingerprint"], "artifacts": {
                  name: {"absolute": str(release / "qualitative" / name),
                         "relative": str((release / "qualitative" / name).relative_to(root))}
                  for name in artifact_names}}
    replacements[str(REPORT / "latest-artifacts.json")] = (json.dumps(latest, indent=2, sort_keys=True) + "\n").encode()
    receipt = extension_receipt(previous_receipt, checks, stage, release, admission, before)
    replacements["reports/publication-build.json"] = (json.dumps(receipt, indent=2, sort_keys=True) + "\n").encode()
    replacements["tex/main.pdf"] = (stage / "tex/main.pdf").read_bytes()
    replacements["tex/main.log"] = (stage / "tex/main.log").read_bytes()
    replacements["tex/main.blg"] = (stage / "tex/main.blg").read_bytes()
    replacements["docs/thesis.pdf"] = (stage / "docs/thesis.pdf").read_bytes()
    with lock(report / "tex-build.lock"):
        if source_hashes(root) != before:
            raise ValueError("Thesis sources changed during build; keeping previous publication")
        if any(file_hash(root / name) != value for name, value in protected_before.items()):
            raise ValueError("Publication PDF, receipt or build artifacts changed during build; keeping current publication")
        check_ownership(root, state)
        for name in exports:
            if name not in state.get("managed_sha256", {}) and (root / name).exists():
                raise ValueError("Unowned output already exists: " + name)
        publish_transaction(root, report, replacements)
    shutil.rmtree(stage)
    return {"phase": "published", **new_state}


def tick(args):
    root, report = ROOT, ROOT / REPORT
    with lock(report / "tex-build.lock"):
        recover_transaction(root, report)
    state = read_json(report / "state.json", {})
    check_ownership(root, state)
    statuses = campaign_statuses()
    names = eligible_stage(statuses)
    result = {"updated_utc": now(), "pid": os.getpid(), "campaigns": statuses,
              "publish_enabled": args.publish, "pending_campaigns": [k for k, v in statuses.items()
                  if v.get("stage") not in {"complete", "completed_no_admissible_configuration"}]}
    if names is None:
        return {**result, "phase": "waiting"}
    stamp = campaign_stamp(names)
    if stamp == state.get("last_processed_input_hash"):
        if file_hash(root / "docs/thesis.pdf") != state.get("pdf_sha256"):
            return {**result, "phase": "publication_changed", "release": state["release"],
                    "note": "PDF changed after extension publication; preserving the user's current PDF."}
        return {**result, "phase": "up_to_date", "release": state["release"]}
    attempt_hash = digest((stamp + json.dumps(source_hashes(root), sort_keys=True)).encode())
    previous = read_json(report / "last-attempt.json", {})
    if previous.get("attempt_hash") == attempt_hash and previous.get("phase") == "staged" and not args.publish:
        return {**result, "phase": "staged", "release": previous["release"]}
    if previous.get("attempt_hash") == attempt_hash and previous.get("phase") == "failed" and not args.retry:
        return {**result, "phase": "needs_review", "error": previous["error"], "attempt_hash": attempt_hash}
    write_json(report / "last-attempt.json", {"attempt_hash": attempt_hash, "phase": "running", "updated_utc": now()})
    try:
        detail = process(root, report, names, args.python, args.publish, state, stamp)
    except Exception as error:
        write_json(report / "last-attempt.json", {"attempt_hash": attempt_hash, "phase": "failed", "error": str(error), "updated_utc": now()})
        raise
    write_json(report / "last-attempt.json", {"attempt_hash": attempt_hash, "phase": detail["phase"],
               "release": detail["release"], "updated_utc": now()})
    return {**result, **detail}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--watch", action="store_true", help="poll every minute; foreground process suitable for nohup")
    parser.add_argument("--publish", action="store_true", help="authorize local managed TeX/PDF updates after all checks pass")
    parser.add_argument("--poll-seconds", type=int, default=60)
    parser.add_argument("--python", type=Path, default=PYTHON, help="existing experiment environment for read-only adapters")
    parser.add_argument("--retry", action="store_true", help="retry the same previously failed input once (not with --watch)")
    args = parser.parse_args()
    if args.poll_seconds < 60 or (args.retry and args.watch):
        parser.error("poll interval must be at least 60 seconds; --retry is one-shot only")
    report = ROOT / REPORT
    stopping = False
    def stop(_signum, _frame):
        nonlocal stopping
        stopping = True
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    try:
        with lock(report / "watcher.lock", blocking=False):
            atomic_bytes(report / "watcher.pid", (str(os.getpid()) + "\n").encode())
            try:
                while not stopping:
                    try:
                        result = tick(args)
                    except Exception as error:
                        result = {"phase": "failed", "error": str(error), "updated_utc": now(), "pid": os.getpid()}
                    write_json(report / "status.json", result)
                    print(json.dumps(result), flush=True)
                    if not args.watch:
                        return 1 if result["phase"] in {"failed", "needs_review"} else 0
                    for _ in range(args.poll_seconds):
                        if stopping:
                            break
                        time.sleep(1)
            finally:
                (report / "watcher.pid").unlink(missing_ok=True)
    except BlockingIOError:
        parser.exit(1, "Another completion coordinator holds watcher.lock\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
