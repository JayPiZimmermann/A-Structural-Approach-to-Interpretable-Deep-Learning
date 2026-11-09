import hashlib
import json
import re
import shutil
from pathlib import Path

base=Path('reports/evidence/new-frontier-review')
contracts=[]
checks=[]
allowed={'propext','Classical.choice','Quot.sound'}
for group in ('smooth','games-global','stopping-structure'):
    manifest=json.loads((base/(group+'-expected-types.json')).read_text())
    log=(base/(group+'-types.log')).read_text()
    exitcode=int((base/(group+'-types.exit')).read_text())
    reports=re.findall(r"depends on axioms:\s*\[([^]]*)\]",log,re.S)
    axioms={re.sub(r'\.\{[^}]*\}', '', a.strip()) for block in reports for a in block.split(',') if a.strip()}
    assert exitcode==0 and 'sorryAx' not in log and 'error:' not in log
    assert len(reports)==len(manifest['targets']) and axioms<=allowed,(group,axioms)
    for item in manifest['targets']:
        contracts.append({'module':item['module'],'declaration':item['declaration'],
          'expected_type':item['expected_type'],'scope':item['scope'],
          'receipt':str(base/(group+'-types.log')),'exact_type_verdict':'pass',
          'assumptions_hidden_by_implicit_binders':False})
    checks.append({'group':group,'contracts':len(reports),'exit':exitcode,'axioms':sorted(axioms),
                   'driver':str(base/(group+'Types.lean'))})

for name in ('boundary','distributional-source','routing-source','stopping-source'):
    assert int((base/(name+'.exit')).read_text())==0,name
    assert 'sorry' not in (base/(name+'.log')).read_text(),name

initial=json.loads((base/'initial-sha256.json').read_text())
changed=[p for p,h in initial.items() if hashlib.sha256(Path(p).read_bytes()).hexdigest()!=h]
assert not changed,changed
extras=['formalization/HiddenMonotonicity/Network.lean',
        'formalization/HiddenMonotonicity/PoolingCircuit.lean',
        'formalization/HiddenMonotonicity/ModernActivationBounds.lean',
        'formalization/Thesis/RoutingGate.lean',
        'tex/chapters/02_foundations.tex','tex/chapters/03_decompositions.tex',
        'tex/chapters/04_game_theory.tex']
for p in extras:
    dest=base/'source'/p;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dest)
sources={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in sorted(set(initial)|set(extras))}
(base/'source-sha256.json').write_text(json.dumps(sources,indent=2)+'\n')

report={
 'schema_version':1,
 'reviewer':'independent adversarial reviewer /root/attack_hidden',
 'review_date':'2026-11-09',
 'verdict':'PASS_WITH_EXPLICIT_SCOPE',
 'summary':'No verified counterexample, circular assumption, changed-target defect, or high-severity semantic gap found in the 54 advertised contracts. This is a scoped review of the new smooth/routing/stopping batches, not certification of every theorem or architectural extension in the thesis.',
 'production_mutations':False,
 'shared_olean_writes':False,
 'prior_reports_modified':False,
 'findings':[],
 'batch_verdicts':[
  {'batch':'smooth','verdict':'pass','source':['tex/chapters/02_foundations.tex:689','tex/chapters/02_foundations.tex:698'],
   'model_correspondence':[
    'HasSecondDistributionalDerivative unfolds to local integrability of f and q and equality of integrals against EVERY compactly supported smooth test. It contains no differentiability, local-AC, reconstruction, or desired lower-bound premise.',
    'The continuous weak-to-classical bridge is substantive: convolution with genuine shrinking normalized bumps proves the zero-second-derivative residual affine; twice-integrated q realizes the weak equation by two integrations by parts. Convex c1/c2 continuity is derived in the source-facing minimality theorem.',
    'The positive and negative curvature are max(deriv(deriv f),0) and max(-deriv(deriv f),0). Canonical components use actual cumulative integrals and the common tilt uses suprema of absolute slopes.',
    'ModernActivation has six formula choices and only positive scale/temperature proof fields. It does not package integrability, convexity or correctness as data. Gaussian GeLU uses the integral of the normalized standard Gaussian density; Mish and Swish are the stated formulas. Analytic regularity/integrability are proved from their formulas.',
    'The completed modern corollary explicitly contains the original softplus convexity and nonnegative curvature clauses. Tanh support and GeLU boundary sign inequalities are correctly inclusive/strict.'
   ]},
  {'batch':'routing','verdict':'pass_for_pure_activation_randomized_routing_source_game',
   'source':['tex/chapters/04_game_theory.tex:1072','tex/chapters/04_game_theory.tex:1126','tex/chapters/04_game_theory.tex:1282'],
   'model_correspondence':[
    'Policy is an actual nonnegative normalized finite probability vector. Positive probability on a nonpositive action mass makes sourceValue bottom; zero probability contributes zero. This avoids misuse of total Real.log at zero.',
    'A routing constructor includes an outside action, making its action type nonempty. Empty streams select pure outside and have bottom source value; nonoutside probabilities are zero even when the displayed denominator is zero.',
    'Strategies contain every contingent off-path choice. Activation choices are Bool; routing choices are arbitrary probability vectors. Reported log-coordinate recursion is separately defined and its bridge to the signed auxiliary recursion is proved for ALL profiles.',
    'The signed saddle is stronger than the reported-log Nash conditions and transfers through monotone logCoordinate. Recursive subgame perfection includes off-path subgames. No saddle or Nash conclusion is assumed by the game constructors.',
    'All nonpositive signed continuation masses tie with stopping in log space, and the selected strategy stops at EVERY such tie, including strict negatives. Both owner copies are handled.',
    'Network construction uses canonical parts of the actual first-layer products x_i*(wp-wn)_ji, preserving signed raw inputs; later activation values are nonnegative. It includes distinct bias and epsilon outside actions, and epsilon cancels between sign branches at theta=1.',
    'The shared Network model has an identity terminal and ReLU at every layer. The new routing theorem covers activated network coordinates, consistently with the source routing section; it does not secretly identify those outputs with arbitrary affine logits.'
   ]},
  {'batch':'stopping','verdict':'pass_for_regions_geometric_paths_and_local_DAG_oracles',
   'source':['tex/chapters/03_decompositions.tex:316','tex/chapters/03_decompositions.tex:327','tex/chapters/04_game_theory.tex:440'],
   'model_correspondence':[
    'Gate regions are defined by equality of the ACTUAL recursively evaluated original gates. The affine extension freezes those gates; monotonicity and nonnegative bias constants are conclusions from nonnegative split parameters.',
    'GeometricPaths has ordinary neuron indices only. Parity XOR is proved equal to Odd of the literal count of negative actual signed edges; its magnitude is the product of absolute signed weights and gates. CanonicalTrace is essential and explicit.',
    'The preactivation formula appends a final ungated affine edge and includes exactly intermediate ReLU gates. Zero edges may occur in the finite enumeration but contribute zero. ZeroBias is explicit for the input-only formula.',
    'Arbitrary intermediate biases are included as a finite list of actual propagated bias stubs; no homogeneous formula is asserted for biased networks.',
    'StoppingCircuit evaluates the existing shared-node Circuit and reads earlier-node streams. Graph ReLU max(a,0) uses right tie-breaking so the zero branch is selected at a tie, exactly reproducing stopPair. General max forwards one entire winning pair.',
    'Addition has a normalized half/half law and discount 2. WTA has a normalized deterministic law and unit discount. Its derivative theorem requires unequal signed operand values, because tied split outputs can be discontinuous even when the recovered scalar max is continuous.'
   ]}
 ],
 'residual_scope':[
  {'id':'SCOPE-ROUTING-AFFINE','classification':'explicit_scope_limit_not_false_claim',
   'location':'formalization/Thesis/RoutingNetwork.lean:187',
   'detail':'No new RoutingNetwork theorem for the separate AffineNetwork terminal readout. Arbitrary signed/bias parameters inside ReLU layers are covered. Source routing theorem is about nonnegative activation outputs.',
   'extension_if_required':'Construct an explicit ungated affine routing output and prove its reported-coordinate bridge before advertising routing equivalence for arbitrary logits.'},
  {'id':'SCOPE-ROUTING-POLICIES','classification':'explicit_scope_limit_not_false_claim',
   'location':'formalization/Thesis/RoutingProfiles.lean:80',
   'detail':'Activation strategies are pure Bool choices. Routing strategies are all normalized randomized policies. No expected-log utility for arbitrary mixed activation policies is defined or claimed by these contracts.',
   'extension_if_required':'Define the desired mixed activation payoff convention explicitly before claiming a behavioral-policy theorem broader than this game.'},
  {'id':'SCOPE-DAG-OCCUPATIONS','classification':'explicit_scope_limit_not_false_claim',
   'location':'formalization/Thesis/StoppingCircuit.lean:160',
   'detail':'DAG recovery/nonnegativity and local addition/WTA occupation derivatives are proved. A complete shared-DAG global derivative/discounted-occupation induction is not among these 15 contracts.',
   'extension_if_required':'Assemble the local pullbacks through the shared Circuit, with explicit differentiability cells/tie conditions, before crediting the global DAG occupation theorem.'},
  {'id':'SCOPE-SWISH-SIGN','classification':'precision_of_contract',
   'location':'formalization/HiddenMonotonicity/ModernSwish.lean:75',
   'detail':'The source phrase positive on a bounded interval around zero and negative in both tails is realized as a positive neighborhood plus two eventually negative tails. The theorem does not separately count curvature roots or prove uniqueness of the positive interval.',
   'extension_if_required':'A stronger exact-root/sign-partition claim would require a separate monotonicity/root argument; the displayed corollary does not quantify that stronger partition.'}
 ],
 'validation':{
  'exact_contracts':checks,
  'targeted_current_source_compiles':['HiddenMonotonicity.DistributionalRegularity','Thesis.RoutingNetwork','Thesis.StoppingPaths'],
  'boundary_driver':str(base/'Boundary.lean'),
  'boundary_exit':0,
  'boundary_cases':['genuine weak-definition unfolding','weak second density q=1 locally integrable example',
   'activation constructors inhabited without analytic premises','no normalized policy on Fin 0',
   'zero stream pure-outside absorption','negative log ties for both players',
   'negative raw input and negative weight with nonzero bias','zero-width biased input layer',
   'two-negative-edge parity and absolute product','graph ReLU tied nonzero streams annihilated',
   'whole-pair WTA tie choice and near-tie jump'],
  'independent_exact_experiment':json.loads((base/'experiment-results.json').read_text()),
  'experiment_note':'The numerical biased affine-readout cases test the independently derived path algebra; they are not credited as a new Lean AffineNetwork routing theorem.',
  'source_snapshot_hashes':str(base/'source-sha256.json'),
  'reviewed_source_changed_during_review':changed
 },
 'reviewed_contracts':contracts,
 'publication_gate_conclusion':'These 54 contracts introduce no identified high-severity blocker. Preserve the explicit residual scopes in coverage metadata; the full build, coverage/status integration, and whole-project publication gate remain root responsibilities.'
}
Path('reports/adversarial-new-frontier-review.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
files=[p for p in base.rglob('*') if p.is_file() and p.name!='evidence-sha256.json']
(base/'evidence-sha256.json').write_text(json.dumps({str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)},indent=2)+'\n')
print('Wrote scoped PASS report for',len(contracts),'contracts; evidence hashes saved.')
