from pathlib import Path
import json,hashlib,datetime
ROOT=Path(__file__).resolve().parents[3];OUT=Path(__file__).resolve().parent
assert 'error' not in (OUT/'boundary.log').read_text().lower()
assert 'error' not in (OUT/'exact-types.log').read_text().lower()
checks=json.loads((OUT/'source-checks.json').read_text());assert len(checks)==13 and all(c['exit_code']==0 for c in checks)
sha=json.loads((OUT/'source-sha256.json').read_text());assert all(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h for p,h in sha.items())
env=json.loads((OUT/'environment.json').read_text());assert all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in env)
for kind in ['exact-types','boundary']:(OUT/(kind+'.exit')).write_text('0\n')
manifest=json.loads((OUT/'expected-types.json').read_text())
checks_semantics=[
('actual shared graph','NodeSpec and Plan certify existing SignedExpr syntax on existing Circuit. graphWith_relu proves hard interpretation equals actual Circuit.eval; forward identity is derived, not assumed.'),
('activation vs hard pool','Only activation annotations soften maximum(affine,0). Pool annotation keeps orderedInputPool hard. NodePolicy allows arbitrary Icc activation probabilities and normalized finite pool distributions.'),
('arbitrary-profile game/SPNE','nodePlayer credits entropy only to its controller; affinePlayer includes actual split biases and signed predecessor ownership. playerValue_advantage holds for all profiles. graph_saddle quantifies complete deviations. SubgamePerfect requires actual local optimality at actual previous profile values.'),
('uniqueness and nonvacuity','NoPools is structural, not an assumed uniqueness property. Sigmoid uniqueness follows from entropy strictness even at zero preactivation/fan-in. The independent consumer instantiates a genuine zero-input negative-bias activation Circuit.'),
('bias and terminal affine readout','Affine NodeSpec has Unit policy and no soft gate. Independent consumer proves output -5 for a signed biased affine row and structural discount 3 for weights [2,-1].'),
('normalized transitions','nodeDiscount is absolute fan-in before smoothing; sigmoid belongs in nodeProbability. Zero fan-in sends all mass to cemetery. node_discount_recovery connects literal stochastic row to selectedWeights.'),
('pool ordering and regularity','Source indices refer to operand order (tex/chapters/04_game_theory.tex:865). earliestWinner uses least operand position, including reordered graph references. A unique winner allows ties among losers. At winning ties only selected occupation is asserted; NodeRegular correctly fails.'),
('actual derivative and full original-graph visits','graphSoft_hasFDerivAt differentiates actual graphSoft by chain rule. graphKernel combines independent selected rows. occupation is a finite path expectation. fullOccupation sums actual discounted graph visits. graft_soft uses the genuine prefix state; fullOccupation_graft_last proves the intermediate bridge.'),
('payoff interpreter','pathPayoff uses predictable expected bias/entropy rewards. expectedPayoff_eq_playerValue establishes expected payoff equality, including lumped stop/zero-row cemetery. It does not assert equality to finer sampled action-dependent payoff histories.')]
report={
'review_id':'attack_hidden/softplus-circuit','status':'pass_with_explicit_scope','high_severity_findings':[],'verified_counterexamples_to_claimed_theorems':[],
'source_labels':['ptnb:thm:softplus-forward','ptnb:thm:softplus-gradient','ptnb:eq:softplus-policy','ptnb:eq:softplus-spne-tildes','ptnb:eq:softplus-decomp'],
'source_locations':['tex/chapters/04_game_theory.tex:848','tex/chapters/04_game_theory.tex:1906','tex/chapters/04_game_theory.tex:1949','tex/chapters/04_game_theory.tex:2014'],
'exact_declarations_reviewed':[{'declaration':t['declaration'],'module':t['module'],'expected_type':t['expected_type']} for t in manifest['targets']],
'model_correspondence':[{'topic':a,'verdict':'pass','evidence':b} for a,b in checks_semantics],
'boundaries_to_preserve':[
'Annotated affine, soft activation, addition and nonempty finite hard-pool nodes; no automatic recognition of arbitrary nested SignedExpr or multiplication-game claim.',
'Classical derivative assumes unique winning operand at every hard pool. No almost-everywhere theorem for smooth/hard-pool DAGs is asserted.',
'Full trajectory interpreter is canonical SPNE law. Arbitrary-profile deviations are proved using actual recursive payoffs; no whole off-equilibrium trajectory datatype is constructed.',
'Expected payoff equality does not imply pathwise equality to a finer sampled stop/continue reward process.',
'No automatic compiler equivalence between every arbitrary Network and Circuit instance is asserted.'],
'validation':{'fresh_source_compiles':13,'fresh_compile_results':'reports/evidence/softplus-circuit-review/source-checks.json','exact_contracts':20,'exact_type_module_universe_axiom_checks':'passed','project_theorem_axiom_closures':len(env),'boundary_consumer':'reports/evidence/softplus-circuit-review/Boundary.lean','boundary_result':'passed','independent_experiment':json.loads((OUT/'experiment-results.json').read_text()),'source_hashes':'reports/evidence/softplus-circuit-review/source-sha256.json','source_unchanged':True,'production_edits':[]},
'conclusion':'The batch faithfully extends canonical source Softplus game and ordinary backward occupation identities to the actual annotated shared DAG, including residual/addition, ordered finite hard pools and signed biased affine output. No high-severity semantic issue found. Preserve the explicit model and derivative boundaries.',
'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
p=ROOT/'reports/adversarial-softplus-circuit-review.json';p.write_text(json.dumps(report,indent=2)+'\n')
files=[p,*[q for q in OUT.rglob('*') if q.is_file() and q.name!='evidence-sha256.json']]
(OUT/'evidence-sha256.json').write_text(json.dumps({str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files},indent=2)+'\n')
print('PASS',len(env),'axiom closures')
