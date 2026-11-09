"""Render manually reviewed contracts through the repository's exact checker.

No inferred declaration type is used as input. This wrapper only selects roots,
records the source closure, and invokes the existing reviewed Lean renderer.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import re

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[3]
DRAFT = OUT.parent / "draft"
FORMAL = ROOT / "formalization"


def atomic_write(path, content):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(content)
    temporary.replace(path)


def main():
    manifest = json.loads((OUT / "expected-types.json").read_text())
    modules = list(dict.fromkeys(target["module"] for target in manifest["targets"]))
    spec = importlib.util.spec_from_file_location("thesis_verify", FORMAL / "scripts/verify.py")
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    driver = verifier.exact_driver({"public_root": modules[0], "targets": manifest["targets"]}, OUT)
    # Replace exactly the single root-import line, preserving the checker body.
    lines = driver.splitlines(keepends=True)
    assert lines[0] == "import " + modules[0] + "\n"
    lines[0] = "".join("import " + module + "\n" for module in modules)
    atomic_write(OUT / "ExactTypes.lean", "".join(lines))
    closure = {}

    def visit(module):
        relative = Path(module.replace(".", "/") + ".lean")
        source = DRAFT / relative
        if not source.is_file():
            source = FORMAL / relative
        if not source.is_file():
            return
        key = str(source.relative_to(ROOT))
        if key in closure:
            return
        closure[key] = hashlib.sha256(source.read_bytes()).hexdigest()
        for dependency in re.findall(r"^import\s+([\w.]+)", source.read_text(), re.M):
            visit(dependency)

    for module in modules:
        visit(module)
    for source in [FORMAL / "lean-toolchain", FORMAL / "lake-manifest.json",
                   FORMAL / "scripts/verify.py", FORMAL / "checks/environment_audit.lean",
                   OUT / "expected-types.json"]:
        closure[str(source.relative_to(ROOT))] = hashlib.sha256(source.read_bytes()).hexdigest()
    atomic_write(OUT / "source-sha256.json", json.dumps(closure, indent=2) + "\n")
    print(len(manifest["targets"]), "manual contracts;", len(closure), "bound source/config files")


if __name__ == "__main__":
    main()
