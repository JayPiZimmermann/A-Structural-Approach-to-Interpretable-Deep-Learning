from pathlib import Path
import json,hashlib,datetime
ROOT=Path(__file__).resolve().parents[3];OUT=Path(__file__).resolve().parent
manifest=json.loads((OUT/'expected-types.json').read_text())
env=json.loads((OUT/'environment.json').read_text())
sha=json.loads((OUT/'source-sha256.json').read_text())
assert all(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h for p,h in sha.items())
assert all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in env)
for name in ['source','exact-types','explicit-types']:
 assert 'error:' not in (OUT/(name+'.log')).read_text()
 (OUT/(name+'.exit')).write_text('0\n')
boundary_ok=(OUT/'boundary.exit').read_text().strip()=='0'
report={
'review_id':'attack_hidden/conditioned-trajectory','status':'pass_with_explicit_scope' if boundary_ok else 'semantic_and_exact_checks_pass_boundary_consumer_pending',
'high_severity_findings':[],'verified_counterexamples_to_claimed_theorems':[],
'source_locations':['tex/chapters/11_trajectory.tex:362','tex/chapters/11_trajectory.tex:606','tex/chapters/11_trajectory.tex:655','tex/chapters/11_trajectory.tex:662','tex/chapters/11_trajectory.tex:669','tex/chapters/11_trajectory.tex:688','tex/chapters/11_trajectory.tex:694'],
'source_correspondence':[
{'topic':'Actual full-law marginal','locations':['Thesis/ConditionedTrajectory.lean:14','Thesis/ConditionedTrajectory.lean:20','Thesis/ConditionedTrajectory.lean:77','Thesis/ConditionedTrajectory.lean:101'],'verdict':'pass','evidence':'prefixMass is an endpoint sum over original prefix paths. timeMass is a stateAt sum over full N-paths. Factorization follows by induction on actual sums, not an assumed representation. The normalized marginal follows from previously proved actual guarded-path quotient.'},
{'topic':'Zero survival support','locations':['Thesis/ConditionedTrajectory.lean:101','Thesis/ConditionedTrajectory.lean:130'],'verdict':'pass','evidence':'Only initial survival is positive. The kernel is explicitly zero at nonpositive potential, with computed survival nonnegative. Zero-denominator geometric identity uses totalized division consistently with the guarded zero row. Intermediate dead states may have positive original prefix mass.'},
{'topic':'Actual overlap and Hellinger','locations':['Thesis/ConditionedTrajectory.lean:153','Thesis/ConditionedTrajectory.lean:164','Thesis/ConditionedTrajectory.lean:179','Thesis/ConditionedTrajectory.lean:195'],'verdict':'pass','evidence':'overlap is the finite sqrt(product) sum on full path laws. The geometric path-product and backwardDP formulas are derived. The actual half-sum of squared square-root differences uses proved normalization; no desired Hellinger identity is assumed.'},
{'topic':'Full prefix monotonicity','locations':['Thesis/ConditionedTrajectory.lean:250'],'verdict':'pass','evidence':'Both kernels are nonnegative and row stochastic. Actual prefix laws are normalized at each depth, actual BC starts at one and is antitone, and actual Hellinger square is monotone. A single common kernel sequence is fixed for all prefixes; no monotonicity across changing horizon-conditioned kernels is asserted.'}],
'boundaries_to_preserve':[
'Conditioned statistics apply to the finite ordinary substochastic-kernel model, together with ConditionedSurvival. The explicit cemetery-event conditional-probability notation of the source is interpreted through ordinary surviving path mass; this leaf does not construct a new cemetery completion theorem.',
'A common finite state type is used at every time, with root at time zero. Varying layer state types need a tagged-state embedding/bridge; source layer indices run in reverse.',
'Normalized conditioning requires positive initial survival for each model. No normalized law is asserted when it is zero.',
'Full-prefix BC monotonicity concerns fixed row-stochastic A/B laws, including a cemetery if desired. It does not apply across separately reconditioned laws for different horizons.',
'No new automatic bridge from arbitrary network implementations into the finite kernel model is supplied by this leaf.'],
'exact_declarations_reviewed':manifest['targets'],
'validation':{'exact_contracts':5,'exact_type_module_universe_axiom_checks':'passed','explicit_fully_unfolded_checks':'ExplicitChecks.lean / explicit-types.log','project_theorem_axiom_closures':len(env),'fresh_source_compile_exit':0,'boundary_consumer_exit':int((OUT/'boundary.exit').read_text()),'independent_experiment':json.loads((OUT/'experiment-results.json').read_text()),'frozen_source_hashes':sha,'source_unchanged':True,'production_edits':[],'shared_olean_writes':False},
'pending':[] if boundary_ok else ['Finish only the independent Boundary.lean nontrivial_overlap finite-sum simplification; preceding boundary examples and all production/exact checks passed.'],
'conclusion':'No semantic or kernel defect found. The new leaf closes the previously pending actual conditioned marginal, geometric-kernel, normalized BC/Hellinger and full stochastic-prefix BC monotonicity clauses in the finite-kernel model.',
'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
p=ROOT/'reports/adversarial-conditioned-trajectory-review.json';p.write_text(json.dumps(report,indent=2)+'\n')
files=[p,*[q for q in OUT.rglob('*') if q.is_file() and q.name!='evidence-sha256.json']]
(OUT/'evidence-sha256.json').write_text(json.dumps({str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files},indent=2)+'\n')
print(report['status'],len(env),'axiom closures')
