#!/usr/bin/env python3
"""Build the complete import root, verify reviewed exact types, and audit every imported project theorem.

The default requires a committed clean source closure. --diagnostic produces explicitly
labelled development evidence. Neither mode equates formal coverage with source coverage.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shlex
import subprocess
import sys
from datetime import datetime, timezone

FORMAL = Path(__file__).resolve().parents[1]
ROOT = FORMAL.parent

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args], text=True).strip()

def local_module(name):
    return FORMAL / (name.replace('.', '/') + '.lean')

def import_closure(root):
    seen, active, ordered = set(), set(), []
    def visit(name):
        p = local_module(name)
        if not p.is_file() or name in seen:
            return
        if name in active:
            raise ValueError('Import cycle at ' + name)
        active.add(name)
        for dep in re.findall(r'^import\s+([\w.]+)', p.read_text(), re.M):
            visit(dep)
        active.remove(name)
        seen.add(name)
        ordered.append(name)
    visit(root)
    return ordered

def source_snapshot(modules):
    paths = [local_module(m) for m in modules]
    paths += [FORMAL / n for n in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                                  'verification.json', 'coverage_map.json', 'tex_links.json',
                                  'scripts/verify.py', 'checks/environment_audit.lean']]
    paths += [ROOT / 'scripts/generate_lean_links.py']
    files = {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in paths}
    dirty = []
    for name in files:
        old = subprocess.run(['git', '-C', str(ROOT), 'show', 'HEAD:' + name], capture_output=True)
        if old.returncode or old.stdout != (ROOT / name).read_bytes():
            dirty.append(name)
    return {'commit': git('rev-parse', 'HEAD'), 'sha256': files,
            'uncommitted_closure_files': dirty}

def exact_driver(manifest, output):
    lines = ['import ' + manifest['public_root'], 'import Lean',
             'set_option autoImplicit false', 'set_option maxHeartbeats 0',
             'open Lean Elab Command', '']
    for i, t in enumerate(manifest['targets']):
        name, module, typ = t['declaration'], t['module'], t['expected_type']
        universes = t.get('universes', [])
        if any(not re.fullmatch(r'[\w.\u2080-\u209f\']+', s) for s in [name, module, *universes]):
            raise ValueError('Invalid Lean name in manifest: ' + name)
        if any(s in typ for s in ['sorry', 'admit', '?_', 'by exact', '/-', '--']):
            raise ValueError('Placeholder or proof/comment syntax in expected type: ' + name)
        marker = '_ThesisExactChecks.target_' + str(i)
        expected_name = '_ThesisExpectedTypes.type_' + str(i)
        kind = t.get('kind', 'theorem')
        if kind not in {'theorem', 'definition'}:
            raise ValueError('Unknown contract kind: ' + kind)
        expected_sort = ' : Prop' if kind == 'theorem' else ''
        marker_kind = 'theorem' if kind == 'theorem' else 'noncomputable def'
        suffix = '.{' + ', '.join(universes) + '}' if universes else ''
        lines += ['section']
        if universes:
            lines += ['universe ' + ' '.join(universes)]
        if t.get('open_namespaces'):
            lines += ['open ' + ' '.join(t['open_namespaces'])]
        if t.get('open_scopes'):
            lines += ['open scoped ' + ' '.join(t['open_scopes'])]
        # Elaborate the proposition in its own declaration, before the target proof can
        # constrain any unresolved terms in the purported expected statement.
        lines += [f'def {expected_name}{expected_sort} := ({typ})',
                  f'{marker_kind} {marker} : {expected_name}{suffix} := by exact @{name}{suffix}', 'end',
                  'run_cmd do', f'  let target ← getConstInfo `{name}',
                  f'  let expected ← getConstInfo `{marker}',
                  f'  unless target.levelParams.length == {len(universes)} && expected.levelParams.length == {len(universes)} do',
                  f'    throwError "Universe arity mismatch: {name}"',
                  '  let env ← getEnv', f'  let some index := env.getModuleIdxFor? `{name} | throwError "Target was not imported"',
                  f'  unless env.header.moduleNames[index.toNat]! == `{module} do',
                  f'    throwError "Defining module mismatch: {name}"',
                  f'  for axiomName in (← Lean.collectAxioms `{marker}) do',
                  '    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do',
                  f'      throwError "Unapproved axiom in exact target {name}: {{axiomName}}"',
                  '  liftTermElabM do',
                  '    let levels := expected.levelParams.map Level.param',
                  '    let targetType := target.type.instantiateLevelParams target.levelParams levels',
                  '    unless ← Meta.isDefEq targetType expected.type do',
                  f'      throwError "Exact type mismatch: {name}"',
                  f'#check @{name}', f'#print axioms {marker}', '']
    template = (FORMAL / 'checks/environment_audit.lean').read_text()
    template = re.sub(r'^import .*\n', '', template, flags=re.M)
    template = template.replace('"../reports/verification/environment.json"',
                                json.dumps(str(output / 'environment.json')))
    lines += [template]
    return '\n'.join(lines) + '\n'

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--diagnostic', action='store_true')
    ap.add_argument('--output', type=Path, default=ROOT / 'reports/verification/current')
    args = ap.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((FORMAL / 'verification.json').read_text())
    target_names = [t['declaration'] for t in manifest['targets']]
    if len(target_names) != len(set(target_names)):
        raise SystemExit('Duplicate exact target contracts')
    linked_names = {t['declaration'] for t in
                    json.loads((FORMAL / 'tex_links.json').read_text()).values()}
    if linked_names - set(target_names):
        raise SystemExit('TeX links without reviewed exact contracts: ' +
                         ', '.join(sorted(linked_names - set(target_names))))
    modules = import_closure(manifest['public_root'])
    topical = {str(p.relative_to(FORMAL).with_suffix('')).replace('/', '.')
               for folder in ['HiddenMonotonicity', 'Thesis']
               for p in (FORMAL / folder).rglob('*.lean')}
    missing = sorted(topical - set(modules))
    if missing:
        raise SystemExit('Production modules unreachable from public root: ' + ', '.join(missing))
    before = source_snapshot(modules)
    if before['uncommitted_closure_files'] and not args.diagnostic:
        raise SystemExit('Clean committed closure required; commit these files or use --diagnostic:\n' +
                         '\n'.join(before['uncommitted_closure_files']))
    receipt = {'started_utc': datetime.now(timezone.utc).isoformat(),
               'mode': 'diagnostic' if args.diagnostic else 'clean_committed',
               'source': before, 'production_modules': modules, 'commands': [],
               'status': 'running', 'exact_target_count': len(manifest['targets']),
               'scope': 'Kernel types and axioms of the recorded closure; source equivalence is separately reviewed in coverage_map.json.'}
    def save():
        (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    def run(label, command):
        log = out / (label + '.log')
        with log.open('w') as stream:
            stream.write('$ ' + shlex.join(command) + '\n')
            stream.flush()
            result = subprocess.run(command, cwd=FORMAL, stdout=stream, stderr=subprocess.STDOUT)
        receipt['commands'].append({'command': command, 'cwd': 'formalization',
                                     'log': log.name, 'exit_code': result.returncode,
                                     'sha256': sha(log.read_bytes())})
        save()
        if result.returncode:
            raise RuntimeError(f'{label} failed; inspect {log}')
    save()
    try:
        # Sequential local-module builds prevent one Lake invocation spawning many heavy elaborators.
        for i, module in enumerate(modules):
            run(f'build-{i:03d}-{module}', ['lake', 'build', '+' + module])
        driver = out / 'ExactTypes.lean'
        driver.write_text(exact_driver(manifest, out))
        run('exact-types-and-environment', ['lake', 'env', 'lean', str(driver)])
        environment = json.loads((out / 'environment.json').read_text())
        actual_names = {r['declaration'] for r in environment}
        spec = importlib.util.spec_from_file_location('lean_links', ROOT / 'scripts/generate_lean_links.py')
        scanner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(scanner)
        declared = set()
        for module in modules:
            for name, d in scanner.declarations(local_module(module).read_text(), module).items():
                if d['kind'] in {'theorem', 'lemma'}:
                    declared.add(name)
        if declared - actual_names:
            raise RuntimeError('Source declarations absent from imported environment: ' + str(sorted(declared - actual_names)))
        allowed = set(manifest['allowed_axioms'])
        for row in environment:
            if set(row['axioms']) - allowed:
                raise RuntimeError('Forbidden axioms: ' + row['declaration'])
        after = source_snapshot(modules)
        if before != after:
            raise RuntimeError('Source closure changed during verification; retry on a stable snapshot')
        receipt.update(status='passed', environment_theorem_count=len(environment),
                       source_theorem_count=len(declared),
                       generated_theorems=sorted(actual_names - declared),
                       secondary_theorems=[{
                           'declaration': row['declaration'], 'module': row['module'],
                           'type_sha256': sha(row['type'].encode()),
                           'module_sha256': before['sha256'][
                               'formalization/' + row['module'].replace('.', '/') + '.lean'],
                           'scope': 'Secondary or generated result: included in the complete axiom audit; not an independently reviewed source-link contract.'
                       } for row in environment if row['declaration'] not in set(target_names)],
                       completed_utc=datetime.now(timezone.utc).isoformat(),
                       artifacts={p.name: sha(p.read_bytes()) for p in [driver, out / 'environment.json']})
    except Exception as exc:
        receipt.update(status='failed', error=str(exc))
        save()
        raise
    save()
    print(f"{receipt['mode']}: {len(modules)} modules; {len(environment)} theorem axiom audits; {len(manifest['targets'])} exact reviewed target types. Receipt: {out / 'receipt.json'}")

if __name__ == '__main__':
    main()
