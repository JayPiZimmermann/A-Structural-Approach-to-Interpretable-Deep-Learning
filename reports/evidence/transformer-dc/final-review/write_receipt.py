"""Record successful independent checks; never infer success from an empty log."""
from pathlib import Path
import hashlib, json, re, subprocess
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['exact','boundary']:
    assert int((OUT/(name+'.exit')).read_text())==0,name
    assert not re.search(r'(^|\n).*\berror:',(OUT/(name+'.log')).read_text()),name
snapshot=json.loads((OUT/'source-snapshot.json').read_text())
assert all(sha(ROOT/p)==h for p,h in snapshot.items()),'source changed during final review'
env=json.loads((OUT/'environment.json').read_text())
axioms=sorted({a for e in env for a in e['axioms']})
assert set(axioms)<= {'propext','Classical.choice','Quot.sound'}
contracts=json.loads((OUT/'contracts.json').read_text())
boundary_count=len(re.findall(r'^example\b',(OUT/'Boundary.lean').read_text(),re.M))
report={
 'status':'pass_with_explicit_scope',
 'reviewer':'/root/transformer_lean_architecture/transformer_final_review',
 'source_commit_at_review':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 'evidence_scope':'Independent diagnostic review of frozen working-tree sources; the clean committed publication gate is owned by the integrating root agent.',
 'exact_contracts':len(contracts['targets']),
 'contract_authoring':'Full-forall expected propositions authored independently from intended mathematical statements and source definitions; no expected types copied from inferred Lean output. The repository exact driver separately checks type, universe arity, defining module and allowed axioms.',
 'exact_exit_code':0,
 'imported_project_theorem_axiom_audits':len(env),
 'allowed_axioms_observed':axioms,
 'boundary_consumers':boundary_count,
 'boundary_exit_code':0,
 'source_sha256':snapshot,
 'semantic_findings':[
  'The Transformer record contains parameters and mathematical domain conditions, not a decomposition invariant or an assumed correct/convex/monotone implementation.',
  'Ordinary forward evaluation explicitly computes signed Q/K/V affine maps, scaled coupled softmax over each nonempty injective key mask, attention-value products, output projections, two residual additions, population-variance epsilon LayerNorm and a supported scalar feed-forward activation.',
  'Blocks are an arbitrary finite List, and the independently proved compiler bridge uses List induction. No numerical upper bound on depth or number of heads occurs in the final theorem.',
  'The recursive Expr split evaluator contains the actual closed-form primitive formulas. Its structural induction uses proved primitive properties; it does not assume the Transformer claim as a premise.',
  'Fixed positional bias, optional final LayerNorm and an unrestricted signed affine output logit are included with the original parameters.',
  'The full doubled-input heads are convex, monotone and nonnegative on the nonnegative orthant. Subtraction reconstructs the original network even outside that orthant, but the structural properties are not enlarged to that domain.',
  'The positive/negative raw-input embedding yields globally convex nonnegative heads and exact signed logits. No false raw-input monotonicity claim is made.',
  'Concrete consumer models establish nonvacuity: negative QKV/output/FFN weights, biases and normalization gains; full and single-key masks; two heads; zero/one/two and arbitrary symbolic depths; optional final normalization; and an explicitly negative affine logit.'
 ],
 'limits':[
  'This is a precise pre-LayerNorm finite inference architecture acting on real token embeddings. It does not claim verification of every architecture named Transformer, tokenization, autoregressive sampling, or a pretrained implementation.',
  'Masks are fixed and nonempty for each query. Fully masked softmax rows are excluded by the model conditions.',
  'Every normalization epsilon is strictly positive; ordinary LayerNorm at epsilon zero is outside the theorem.',
  'Heads may have arbitrary positive key/value widths. A constant real logit scale is a parameter; the usual reciprocal-square-root width scale is one permitted choice.',
  'The expression compiler is not a verified shared-DAG compiler. No constant-factor memory/work bound, floating-point accuracy, numerical stability, or runtime theorem is proved.',
  'The axiom audit count concerns imported project theorem constants, not 920 independent mathematical thesis theorems.'
 ],
 'artifacts':{name:sha(OUT/name) for name in ['contracts.json','Exact.lean','exact.log','exact.exit','environment.json','Boundary.lean','boundary.log','boundary.exit','write_checks.py']}
}
(OUT/'review.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['status','exact_contracts','imported_project_theorem_axiom_audits','boundary_consumers']}))
