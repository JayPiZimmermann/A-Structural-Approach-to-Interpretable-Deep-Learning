from pathlib import Path
import json,hashlib,shutil,datetime,re
mods=['AffineHeads','AffineChunk','MaxPool','PoolingCircuit','DifferentiableHeads','AlmostEverywhere','PrefixSources','DifferentiableBackward']
scratch=Path('formalization/.lake/diagnostics/new-hidden-audit')
e=Path('reports/evidence/hidden-recheck');(e/'source').mkdir(parents=True,exist_ok=True)
for f in ['RepairTypes.lean','repair-types.log','repair-types.exit','Boundary.lean','boundary.log','boundary.exit','OlderTypes.lean','older-types.log','older-types.exit','older_contracts.py','support_audit.py','support_audit.json','support.log','write_recheck.py']:
 shutil.copy2(scratch/f,e/f)
for mod in mods:
 shutil.copy2(Path('formalization/HiddenMonotonicity')/(mod+'.lean'),e/'source'/(mod+'.lean'))
 for suffix in ['log','exit']:shutil.copy2(scratch/'source-build'/(mod+'.'+suffix),e/(mod+'.'+suffix))
for f in ['reports/hidden-expected-types.json','reports/hidden-recheck-expected-types.json']:shutil.copy2(f,e/Path(f).name)
for name in ['repair-types','older-types','boundary']:
 assert (scratch/(name+'.exit')).read_text().strip()=='0'
 assert 'sorryAx' not in (scratch/(name+'.log')).read_text()
for mod in mods:assert (scratch/'source-build'/(mod+'.exit')).read_text().strip()=='0'

claims=json.loads(Path('reports/hidden-expected-types.json').read_text())['targets']
old=json.loads(Path('reports/hidden-recheck-expected-types.json').read_text())['targets']
sourceverdicts=[
{'module':'DifferentiableHeads','verdict':'PASS','reviewed_mechanism':'layerJac chooses a genuinely maximizing affine branch even at ties. The single-layer touching affine lower bound is explicit. Nonnegative split weights make every downstream selected Jacobian monotone, so the support inequality composes. The scalar support lemma applies Fermat to f(y)-D(y-x) at its actual local minimum; differentiability identifies D with the genuine Frechet derivative. There is no assumed derivative recurrence or circular support definition. Balanced lifting is applied to the support itself, so differentiability of the full pair-input head is not silently required.'},
{'module':'AlmostEverywhere','verdict':'PASS','reviewed_mechanism':'Actual split and affine-head functions have explicit global Lipschitz bounds. Rademacher is applied with volume in the original finite-dimensional input space. Both head coordinates are covered by differentiability of one pair-valued Lipschitz map. The backward invariant quantifies all shifts after a single full-measure event. No Strict premise or assumed null zero-preactivation set appears.'},
{'module':'PrefixSources','verdict':'PASS','reviewed_mechanism':'append recursively preserves the actual Network layers, with explicit eval-composition and selected-Jacobian-composition equalities. originalTrace_ae_derivative is obtained coordinatewise from actual affine-head derivatives and their exact difference recovery, not assumed. Each minimum is the actual preactivation minus the next appended ReLU prefix. The induction always keeps the original domain Vec a and appends to the prefix. It never pulls an a.e theorem back through a possibly singular activation map. q.value retains the full variable prefix; only q.jacobian freezes the selected trace at the differentiation point. The canonical absolute-tail equality is inherited explicitly.'},
{'module':'DifferentiableBackward','verdict':'PASS','reviewed_mechanism':'affine_Q_row_formulas is the all-input algebraic identity for the existing implemented shifted pass. affine_Q_closed_form_ae intersects the actual-Q and actual-original derivative events, then attaches the affine readout. affine_plain_Q_gradients_ae adds actual derivatives of both head functions on a common full-measure set. The pointwise differentiable-head formula intentionally uses selected Q rows without claiming differentiability of every unused Q function; this distinction is necessary and explicitly stated.'},
{'module':'AffineHeads','verdict':'PASS','reviewed_mechanism':'The functions are exactly G=rp(splitPlus)+rn(splitMinus)+bp and H=rn(splitPlus)+rp(splitMinus)+bn. Their difference equals (rp-rn)(eval)+(bp-bn). The readout is genuinely ungated, can give negative logits and has no final minimum/Q source. Zero-shift terminal seeds are proved to differentiate these actual heads. The balanced derivative has the required factor 1/2. coefficientRow sign-sum and sign-difference bridge canonical readout parts to literal absolute and signed coefficient rows.'},
{'module':'AffineChunk','verdict':'PASS','reviewed_mechanism':'affineChunk is the ungated pair (preP+bp,preN+bn). Recovery is affineLayer, not ReLU. Nonnegativity uses the explicit nonnegative parameter/input assumptions. Exact affine interpolation and ConvexOn do not require nonnegative biases, and their separate lemmas correctly omit that restriction.'},
{'module':'MaxPool','verdict':'PASS','reviewed_mechanism':'finitePool is exactly the finite nonempty sup/erase-sum construction from the source. The bundled theorem includes recovery, positivity, monotonicity and both convexity claims. PoolWinner is a true global maximizing-index predicate; existence is proved; winnerPool forwards both stream coordinates at the same certified maximizing index. It is no longer the previous tautological arbitrary-index equality.'},
{'module':'PoolingCircuit','verdict':'PASS','reviewed_mechanism':'winnerPair compares the two represented differences and forwards an entire pair, with deterministic left tie breaking. poolTreeSplit recursively selects through top-level nested maximum trees, forwarding a real winning leaf argument pair. Non-max arithmetic uses the existing correct split. splitWithPolicy reuses prior-node values and independently chooses pooling/recentering by each appended node index. All-node recovery/nonnegativity and the literal convex-policy compatibility bridge are proved. No unsupported shape claim is made for WTA or recentering.'}
]
reviewed=[]
for mod in mods:
 p=Path('formalization/HiddenMonotonicity')/(mod+'.lean');ns=[]
 for i,line in enumerate(p.read_text().splitlines(),1):
  m=re.match(r'namespace\s+(\S+)',line)
  if m:ns.append(m.group(1));continue
  if re.match(r'end(?:\s|$)',line):
   if ns:ns.pop()
   continue
  m=re.match(r'(?:@\[[^]]*\]\s*)?(?:noncomputable\s+)?(theorem|def|inductive|structure|abbrev)\s+([^\s:{]+)',line)
  if m:reviewed.append({'declaration':'.'.join(ns+[m.group(2)]),'kind':m.group(1),'file':str(p),'line':i})
report={
'audit':'Independent adversarial re-review of Hidden Monotonicity repairs',
'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
'reviewer':'/root/attack_hidden',
'verdict':'PASS for the focused eight-module semantic repair review. No critical or high-severity finding remains in these modules, no false repaired theorem or hidden/vacuous main premise was found, and the reviewed source-to-model bridges are genuine. This is a diagnostic semantic/type/axiom/source-compilation receipt, not the root clean-closure publication gate.',
'findings':[],
'resolved_original_findings':[
{'id':'HM-01','status':'resolved_at_claimed_scope','evidence':'The new pointwise differentiable-head support theorem and original-domain Rademacher/prefix-Q arguments remove Strict. Both identically-zero networks and persistent zero gates are admitted. All individual Q derivatives are certified a.e, with a necessary distinction at exceptional points.'},
{'id':'HM-02','status':'resolved','evidence':'Actual affine heads/logit, readout-bias recovery, true head derivatives, canonical readout mass and both shifted partial invariants are now defined and proved.'},
{'id':'HM-04','status':'resolved','evidence':'The linked affine-chunk theorem now proves the actual ungated affine function and complete property bundle.'},
{'id':'HM-05','status':'resolved_for_scalar_graph_model','evidence':'Actual maximizing-WTA semantics and independent per-node recentering are integrated into the same shared-node Circuit interpreter.'},
{'id':'HM-06','status':'resolved','evidence':'The precise finite pool pair now has recovery, nonnegative-output, monotonicity and convexity theorems.'},
{'id':'HM-03/HM-07/HM-08','status':'root_manuscript_repairs_observed','evidence':'The current saliency text has the suffix bulk factor; current masks use strict positivity/inactive zero; the eta-zero source remark has been revised. These were manuscript responsibilities, not new Lean-proof changes.'}
],
'module_verdicts':sourceverdicts,
'nonblocking_scope_notes':[
'At a point where only final heads are differentiable, an unused Q function can still have a kink. The repair correctly does not assert every Q derivative at every such point. Zero readout with Q(x)=min(x,0) at zero is an explicit control showing why this distinction must remain in source links.',
'For affine_Q_closed_form_ae, shifts and readout parameters are fixed before the a.e input quantifier. For affine_ae_backward_invariants, all shifts occur after one common full-measure event. These are the actual printed quantifier orders; no uncountable-intersection step is used.',
'The arbitrary signed rp/rn theorem affine_Q_closed_form_ae certifies the original-logit derivative and shifted algorithmic identities. Actual plain-head derivative statements additionally require monotone rp/rn; canonical coefficient rows discharge this genuine positivity condition.',
'Convex and winner finite-pool implementations may choose different common stream levels; winnerPool uses an arbitrary certified maximizing index while poolTreeSplit has deterministic left tie breaking. Both meet the source shared-winning-index semantics, which imposes no unique tie index.',
'Concrete tensor flattening, end-to-end converter correctness, and the graph-size bound remain outside these eight repairs; current coverage_map marks the CNN/source-size coverage partial. This focused PASS is not an assertion that the whole thesis is completely formalized.',
'Stale mass/complementarity equation links were reported during this review and the root corrected them to affine_canonical_mass before the final snapshot. Older strict projection-head helper contracts remain valid within their stated scope.'
],
'exact_checked_new_declarations':[x['declaration'] for x in claims],
'older_reviewed_contracts':{'manifest':'reports/hidden-recheck-expected-types.json','count':len(old),'declarations':[x['declaration'] for x in old],'definition_target':'HiddenMonotonicity.MaskedTrace.stabilized','note':'Independently restated after inspecting definitions and statements. Expected types were not altered to resolve compilation failures; only the checking driver was placed in a noncomputable section for the definition target.'},
'source_declarations_reviewed':reviewed,
'verification':{
'new_exact_types':{'count':len(claims),'exit_code':0,'driver':str(e/'RepairTypes.lean'),'receipt':str(e/'repair-types.log')},
'older_exact_types':{'count':len(old),'exit_code':0,'driver':str(e/'OlderTypes.lean'),'receipt':str(e/'older-types.log')},
'axioms':'Every exact-checked proposition/definition has only propext, Classical.choice and Quot.sound. No accidental auto-bound mathematical parameter or forbidden axiom appeared in the explicit #check @ receipts.',
'boundary':{'exit_code':0,'driver':str(e/'Boundary.lean'),'receipt':str(e/'boundary.log'),'checks':['canonical zero network never Strict yet actual head derivative for every input with unequal readout biases','repeated ReLU has a tied second gate on the entire negative halfline and still satisfies the global support theorem','negative affine logit and distinct nonnegative head values with unequal biases','nested WTA forwards (2,0) among (10,9),(2,0),(100,99)','left tie breaking forwards one entire tied pair','different policies on successive shared graph nodes give intended actual outputs']},
'source_compilation':{'modules':mods,'exit_codes':{m:0 for m in mods},'command':'cd formalization; lake env lean -o .lake/diagnostics/new-hidden-audit/source-build/MODULE.olean HiddenMonotonicity/MODULE.lean','note':'All eight actual current source files were independently compiled, writing only audit scratch artifacts. Dependency imports used the current shared cache; root committed clean-closure gate remains separate.'},
'independent_exact_experiment':json.loads((e/'support_audit.json').read_text()),
'reproduce_experiment':'python3 reports/evidence/hidden-recheck/support_audit.py',
'reproduce_types':'The saved drivers can be copied to formalization/.lake/diagnostics/new-hidden-audit and checked with lake env lean. Expected-type JSON manifests reproduce all examples and #check/#print axioms receipts.'
},
'evidence_directory':str(e),
'original_audit_preserved':{'file':'reports/adversarial-hidden.json','sha256':hashlib.sha256(Path('reports/adversarial-hidden.json').read_bytes()).hexdigest(),'note':'Not modified by this re-review.'},
'limitations':['Read-only production audit; no production sources or shared oleans were written.','Finite exhaustive tests cover the stated finite sample and are not universal certificates; universal statements are established by the reviewed Lean proofs.','Root public import, exact manifest and committed clean-source reproducibility gates are independent responsibilities.']
}
Path('reports/adversarial-hidden-recheck.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
paths=list(e.rglob('*'))+[Path('reports/hidden-expected-types.json'),Path('reports/hidden-recheck-expected-types.json'),Path('reports/hidden-repairs.md'),Path('reports/adversarial-hidden.json'),Path('reports/adversarial-hidden-recheck.json'),Path('formalization/coverage_map.json'),Path('formalization/tex_links.json'),Path('formalization/lean-toolchain'),Path('formalization/lakefile.toml'),Path('tex/chapters/03_decompositions.tex'),Path('tex/chapters/05_saliency.tex')]+list(Path('formalization/HiddenMonotonicity').glob('*.lean'))
hashes={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths) if p.is_file() and p.name!='sha256.json'}
(e/'sha256.json').write_text(json.dumps(hashes,indent=2)+'\n')
print(json.dumps({'report':'reports/adversarial-hidden-recheck.json','new_types':len(claims),'older_types':len(old),'reviewed_source_declarations':len(reviewed),'source_compiles':len(mods),'findings':0}))
