#!/usr/bin/env python3
"""Fixture tests for the completion coordinator; no experiments or TeX builds."""
import importlib.util
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("coordinator", Path(__file__).with_name("complete_vit_extension.py"))
C = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(C)


class CoordinatorTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.report = self.root / C.REPORT
        self.chapter = self.root / C.CHAPTER
        self.chapter.parent.mkdir(parents=True)
        self.original = "Original experiments.\n" + C.ANCHOR + "\n"
        self.chapter.write_text(self.original)
        (self.root / "docs").mkdir()
        (self.root / "docs/thesis.pdf").write_bytes(b"previous valid PDF")

    def test_gate_requires_cam_and_split_complete_without_failure(self):
        complete = {"stage": "complete", "failures": []}
        pending = {"stage": "test_robustness"}
        self.assertIsNone(C.eligible_stage({"cam": complete, "paper": pending}))
        self.assertIsNone(C.eligible_stage({"cam": complete, "paper": {**complete, "failures": ["metric"]}}))
        self.assertEqual(C.eligible_stage({"cam": complete, "paper": complete, "weaker": pending}), ("cam", "paper"))
        self.assertEqual(C.eligible_stage(dict.fromkeys(("cam", "paper", "weaker"), complete)), ("cam", "paper", "weaker"))

    def test_span_idempotence_and_outside_edits_preserved(self):
        first, sha = C.update_chapter(self.original, None)
        second, sha2 = C.update_chapter("User paragraph.\n" + first, sha)
        self.assertEqual(second, "User paragraph.\n" + first)
        self.assertEqual(sha2, sha)
        self.assertEqual(second.count(C.INPUT), 1)

    def test_edited_removed_and_unowned_spans_refused(self):
        first, sha = C.update_chapter(self.original, None)
        for text, previous in ((first.replace(C.INPUT, "user content"), sha),
                               (self.original, sha), (first, None)):
            with self.subTest(text=text):
                with self.assertRaises(ValueError):
                    C.update_chapter(text, previous)
        with self.assertRaises(ValueError):
            C.update_chapter(self.original + C.ANCHOR, None)

    def test_managed_file_edit_refused_even_without_new_results(self):
        text, sha = C.update_chapter(self.original, None)
        self.chapter.write_text(text)
        table = self.root / C.PREFIX / "integration.tex"
        table.parent.mkdir(parents=True)
        table.write_text("original table")
        state = {"span_sha256": sha, "managed_sha256": {str(table.relative_to(self.root)): C.file_hash(table)}}
        C.check_ownership(self.root, state)
        table.write_text("user changed table")
        with self.assertRaises(ValueError):
            C.check_ownership(self.root, state)

    def test_partial_publication_rolls_back_existing_and_new_files(self):
        replacements = {str(C.PREFIX / "integration.tex"): b"new table",
                        str(C.CHAPTER): b"new chapter", "docs/thesis.pdf": b"new PDF"}
        with self.assertRaises(RuntimeError):
            C.publish_transaction(self.root, self.report, replacements, fail_after=2)
        self.assertEqual(self.chapter.read_text(), self.original)
        self.assertEqual((self.root / "docs/thesis.pdf").read_bytes(), b"previous valid PDF")
        self.assertFalse((self.root / C.PREFIX / "integration.tex").exists())
        self.assertFalse((self.report / "transaction.json").exists())

    def test_successful_transaction_and_idempotent_recovery(self):
        C.publish_transaction(self.root, self.report, {"docs/thesis.pdf": b"validated PDF"})
        C.recover_transaction(self.root, self.report)
        self.assertEqual((self.root / "docs/thesis.pdf").read_bytes(), b"validated PDF")

    def test_crash_recovery_refuses_subsequent_user_edit(self):
        backup = self.report / "rollback/0"
        backup.parent.mkdir(parents=True)
        backup.write_bytes(b"previous valid PDF")
        C.write_json(self.report / "transaction.json", {"phase": "prepared", "files": [{
            "path": "docs/thesis.pdf", "before": C.digest(b"previous valid PDF"),
            "after": C.digest(b"new PDF"), "backup": "rollback/0"}]})
        (self.root / "docs/thesis.pdf").write_bytes(b"user replaced PDF")
        with self.assertRaises(ValueError):
            C.recover_transaction(self.root, self.report)
        self.assertEqual((self.root / "docs/thesis.pdf").read_bytes(), b"user replaced PDF")
        # Once the journal's own staged file is restored, recovery is safe.
        (self.root / "docs/thesis.pdf").write_bytes(b"new PDF")
        C.recover_transaction(self.root, self.report)
        self.assertEqual((self.root / "docs/thesis.pdf").read_bytes(), b"previous valid PDF")

    def test_path_traversal_rejected(self):
        for path in ("/tmp/escape", "../escape", "a/../../escape"):
            with self.assertRaises(ValueError):
                C.safe_relative(path)

    def test_symlink_ancestor_cannot_redirect_publication(self):
        elsewhere = self.root / "elsewhere"
        elsewhere.mkdir()
        (self.root / "redirect").symlink_to(elsewhere, target_is_directory=True)
        with self.assertRaises(ValueError):
            C.publish_transaction(self.root, self.report, {"redirect/file": b"unexpected"})
        self.assertFalse((elsewhere / "file").exists())

    def statistics_fixture(self):
        rows = ["gradient__cr-maxabs", "splitcam_selected"]
        metrics = {}
        row_metrics = {}
        for name in ("AL", "PG", "TK", "PF5", "PF20", "Sel", "MaxS", "AvgS"):
            n = 200 if name in {"MaxS", "AvgS"} else 565
            value = {"mean": 1., "lo": .8, "hi": 1.2, "n": n}
            row_metrics[name] = {**value, "coverage": 1.}
            metrics[name] = {"rows": {r: dict(value) for r in rows}, "family_size": 1,
                             "pairs": [{"left": rows[0], "right": rows[1], "p": .5, "p_holm": .5, "n": n}]}
        statistics = {"family_rows": rows, "metadata": {"historical_gradient": "Archived values rounded to six digits."}, "metrics": metrics}
        output = self.report / "fixture"
        C.write_json(output / "combined_statistics.json", statistics)
        admission = {"ready": True, "source_fingerprint": "fixture", "requested_campaigns": ["cam", "paper"],
                     "campaigns": [{"name": n, "ready": True, "issues": []} for n in ("cam", "paper")],
                     "n_rows": 2, "rows": [{"row_label": rows[1], "campaign": "paper", "metrics": row_metrics,
                                             "runtime": {"n_images": "50", "failures": "0"}}],
                     "combined_statistics": {"status": "complete", "path": "combined_statistics.json", "family_rows": rows,
                                             "sha256": C.file_hash(output / "combined_statistics.json")},
                     "exported_files": {name: str(C.PREFIX.relative_to("tex") / name)
                                        for name in ("integration.tex", "extension_ci_longtable.tex")}}
        for name in admission["exported_files"]:
            (output / name).write_text("fixture TeX")
        C.write_json(output / "admission.json", admission)
        return admission, statistics, output

    def test_combined_statistics_require_exact_whole_displayed_family(self):
        admission, statistics, output = self.statistics_fixture()
        C.validate_statistics(admission, output)
        statistics["family_rows"].append("undisplayed row")
        C.write_json(output / "combined_statistics.json", statistics)
        admission["combined_statistics"]["sha256"] = C.file_hash(output / "combined_statistics.json")
        with self.assertRaisesRegex(ValueError, "family"):
            C.validate_statistics(admission, output)

    def test_admission_rejects_incomplete_metrics_and_pending_statistics(self):
        admission, _, output = self.statistics_fixture()
        with patch.object(C, "run", return_value=0):
            C.audit_export(self.root, output, ("cam", "paper"), "python")
            admission["rows"][0]["metrics"]["MaxS"]["n"] = 199
            C.write_json(output / "admission.json", admission)
            with self.assertRaisesRegex(ValueError, "quantitative cell"):
                C.audit_export(self.root, output, ("cam", "paper"), "python")
            admission["rows"][0]["metrics"]["MaxS"]["n"] = 200
            admission["combined_statistics"]["status"] = "pending"
            C.write_json(output / "admission.json", admission)
            with self.assertRaisesRegex(ValueError, "statistics are incomplete"):
                C.audit_export(self.root, output, ("cam", "paper"), "python")

    def test_already_published_tick_is_idempotent_and_preserves_new_pdf(self):
        chapter, span = C.update_chapter(self.original, None)
        self.chapter.write_text(chapter)
        state = {"span_sha256": span, "managed_sha256": {}, "last_processed_input_hash": "same", "release": "fixture",
                 "pdf_sha256": C.file_hash(self.root / "docs/thesis.pdf")}
        C.write_json(self.report / "state.json", state)
        args = SimpleNamespace(publish=True, retry=False)
        with patch.object(C, "ROOT", self.root), patch.object(C, "campaign_statuses", return_value={}), \
             patch.object(C, "eligible_stage", return_value=("cam", "paper")), \
             patch.object(C, "campaign_stamp", return_value="same"), patch.object(C, "process") as process:
            self.assertEqual(C.tick(args)["phase"], "up_to_date")
            (self.root / "docs/thesis.pdf").write_bytes(b"user updated PDF")
            self.assertEqual(C.tick(args)["phase"], "publication_changed")
            process.assert_not_called()
        self.assertEqual((self.root / "docs/thesis.pdf").read_bytes(), b"user updated PDF")

    def test_staging_watch_does_not_repeat_completed_render(self):
        hashes = {"fixture": "same"}
        attempt = C.digest(("same" + json.dumps(hashes, sort_keys=True)).encode())
        C.write_json(self.report / "last-attempt.json", {"attempt_hash": attempt, "phase": "staged", "release": "fixture"})
        args = SimpleNamespace(publish=False, retry=False)
        with patch.object(C, "ROOT", self.root), patch.object(C, "campaign_statuses", return_value={}), \
             patch.object(C, "eligible_stage", return_value=("cam", "paper")), \
             patch.object(C, "campaign_stamp", return_value="same"), \
             patch.object(C, "source_hashes", return_value=hashes), patch.object(C, "process") as process:
            self.assertEqual(C.tick(args)["phase"], "staged")
            process.assert_not_called()

    def test_user_pdf_changed_during_build_is_not_overwritten(self):
        exports = {str(C.PREFIX / "integration.tex"): b"new table"}
        def fake_snapshot(root, stage):
            (stage / C.CHAPTER).parent.mkdir(parents=True)
            (stage / C.CHAPTER).write_text(self.original)
            return {"fixture": "same"}
        def fake_build(stage):
            (stage / "docs").mkdir()
            (stage / "docs/thesis.pdf").write_bytes(b"candidate PDF")
            for name in ("main.pdf", "main.log", "main.blg"):
                (stage / "tex" / name).write_bytes(b"candidate PDF")
            (self.root / "docs/thesis.pdf").write_bytes(b"user updated PDF")
            result = {"status": "passed", "documents": {"thesis.pdf": {"pages": 149, "sha256": C.digest(b"candidate PDF")}}, "checks": {}}
            C.write_json(stage.parent / "publication-checks.json", result)
            return result
        with patch.object(C, "audit_export", return_value=({"source_fingerprint": "fixture"}, exports)), \
             patch.object(C, "render_candidates", return_value={"count": 10}), \
             patch.object(C, "snapshot", side_effect=fake_snapshot), \
             patch.object(C, "build_snapshot", side_effect=fake_build), \
             patch.object(C, "source_hashes", return_value={"fixture": "same"}), \
             patch.object(C, "campaign_stamp", return_value="fixture"):
            with self.assertRaisesRegex(ValueError, "artifacts changed"):
                C.process(self.root, self.report, ("cam", "paper"), "python", True, {}, "fixture")
        self.assertEqual(self.chapter.read_text(), self.original)
        self.assertEqual((self.root / "docs/thesis.pdf").read_bytes(), b"user updated PDF")

    def test_failed_isolated_build_never_changes_publication(self):
        exports = {str(C.PREFIX / "integration.tex"): b"new table"}
        def fake_snapshot(root, stage):
            (stage / C.CHAPTER).parent.mkdir(parents=True)
            (stage / C.CHAPTER).write_text(self.original)
            return {}
        with patch.object(C, "audit_export", return_value=({"source_fingerprint": "fixture"}, exports)), \
             patch.object(C, "render_candidates", return_value={"count": 10}), \
             patch.object(C, "snapshot", side_effect=fake_snapshot), \
             patch.object(C, "build_snapshot", side_effect=ValueError("fixture: 151 pages")):
            with self.assertRaisesRegex(ValueError, "151 pages"):
                C.process(self.root, self.report, ("cam", "paper"), "python", True, {}, "fixture")
        self.assertEqual(self.chapter.read_text(), self.original)
        self.assertEqual((self.root / "docs/thesis.pdf").read_bytes(), b"previous valid PDF")
        self.assertFalse((self.root / C.PREFIX / "integration.tex").exists())

    def test_successful_staged_build_publishes_and_records_hashes(self):
        exports = {str(C.PREFIX / "integration.tex"): b"new table"}
        def fake_snapshot(root, stage):
            (stage / C.CHAPTER).parent.mkdir(parents=True)
            (stage / C.CHAPTER).write_text(self.original)
            return {"fixture": "same"}
        def fake_build(stage):
            (stage / "docs").mkdir()
            (stage / "docs/thesis.pdf").write_bytes(b"validated PDF")
            for name in ("main.pdf", "main.log", "main.blg"):
                (stage / "tex" / name).write_bytes(b"validated PDF" if name.endswith("pdf") else b"clean")
            result = {"status": "passed", "documents": {"thesis.pdf": {"pages": 149, "sha256": C.digest(b"validated PDF")}}, "checks": {"fixture_passed": True}}
            C.write_json(stage.parent / "publication-checks.json", result)
            return result
        with patch.object(C, "audit_export", return_value=({"source_fingerprint": "fixture"}, exports)), \
             patch.object(C, "render_candidates", return_value={"count": 10}), \
             patch.object(C, "snapshot", side_effect=fake_snapshot), \
             patch.object(C, "build_snapshot", side_effect=fake_build), \
             patch.object(C, "source_hashes", return_value={"fixture": "same"}), \
             patch.object(C, "campaign_stamp", return_value="fixture"):
            result = C.process(self.root, self.report, ("cam", "paper"), "python", True, {}, "fixture")
        self.assertEqual(result["phase"], "published")
        self.assertEqual(result["pages"], 149)
        self.assertEqual((self.root / "docs/thesis.pdf").read_bytes(), b"validated PDF")
        state = C.read_json(self.report / "state.json")
        C.check_ownership(self.root, state)
        self.assertEqual(state["last_processed_input_hash"], "fixture")
        self.assertEqual(self.chapter.read_text().count(C.INPUT), 1)
        latest = C.read_json(self.report / "latest-artifacts.json")
        self.assertEqual(len([name for name in latest["artifacts"] if name.startswith("candidate_")]), 10)
        receipt = C.read_json(self.root / "reports/publication-build.json")
        self.assertEqual(receipt["pdf_sha256"], C.digest(b"validated PDF"))
        self.assertEqual(receipt["pages"], 149)


if __name__ == "__main__":
    unittest.main(verbosity=2)
