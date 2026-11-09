from pathlib import Path
import hashlib,json,re,datetime
root=Path('.'); evidence=Path('reports/evidence/attack_hidden')

def loc(file,needle):
    lines=Path(file).read_text().splitlines()
    return {'file':file,'line':next(i+1 for i,s in enumerate(lines) if needle in s)}
def L(mod,name):return loc('formalization/HiddenMonotonicity/'+mod+'.lean',name)
def T(ch,needle):return loc('tex/chapters/'+ch+'.tex',needle)
findings=[
{
'id':'HM-01','severity':'high','classification':'definite_formal_scope_gap','title':'Strict gates exclude smooth admissible networks on open sets, not merely kink points',
'source_locations':[T('05_saliency','statements involving derivatives hold at every differentiability point')],
'lean_locations':[L('OriginalTrace','def Network.Strict'),L('NetworkDerivative','theorem Network.hasFDerivAt_split'),L('BackwardStatements','theorem Network.plain_head_gradient_formulas'),L('QsOuRcEs'.replace('QsOuRcEs','QSources'),'theorem Network.stabilized_backward_absolute_Q_closed_form')],
'evidence':'The Lean premise requires every preactivation in every layer to be nonzero. A canonical Network 1 1 with Wp=Wn=bp=bn=0 and identity tail has constant original output and constant split heads everywhere, but Strict x is false for every x. Checks.lean kernel-checks both facts and HasFDerivAt of the whole split map. Thus the current source-linked result does not establish the advertised every-differentiability-point or almost-everywhere theorem for arbitrary networks. The theorem family is not globally vacuous: the rational audit includes 556 satisfiable strict instances.',
'minimal_repair':'Prove derivative identities on genuine differentiability/cell conditions that admit locally identically zero preactivations, and then establish the intended almost-everywhere corollary. Alternatively state strict-gate scope in the manuscript, but that would retain a restriction relative to the requested complete theorem. Do not claim Strict holds a.e. merely because the network is CPWL.',
'not_a_counterexample_to_lean':True,'metadata_verdict':'coverage_map states strict scope honestly; this is missing source scope, not hidden proof fraud.'
},
{
'id':'HM-02','severity':'high','classification':'definite_model_and_source_link_gap','title':'Final affine logits are inconsistent across source sections and not fully bridged to the split-head derivative API',
'source_locations':[T('03_decompositions','with scalar output'),T('03_decompositions','for $0 \\le l < L$,'),T('05_saliency','The readout layer $L$'),T('05_saliency','With the activation masks')],
'lean_locations':[L('Network','def Network.eval'),L('AffineReadout','def affineReadoutSeed'),L('AffineReadout','theorem Network.affine_readout_closed_form'),L('AffineReadout','theorem Network.affine_logit_derivative'),L('BackwardStatements','theorem Network.plain_head_gradient_formulas'),L('OriginalTrace','theorem Network.sensitivity_complementarity_absolute')],
'evidence':'Network.layer applies ReLU at every layer and Network.output is identity. Chapter 03 uses the same fully activated output convention. Chapter 05 then explicitly calls L an ungated affine logit, yet its recursion quantifies l=L-1 and uses M^(L,+/-), after defining masks only for hidden layers. The formal affine-readout formula is real algebra, not a fake assumption: it supports arbitrary terminal partial seeds and separately differentiates the signed logit. However it never defines the corresponding affine split-head functions or proves that its zero-shift seed run is their HasFDerivAt; main source-linked head, mass, and partial-invariant declarations still concern projection heads of the fully gated Network. Neither rPlus/rMinus positivity nor their canonical entrywise sign-part bridge to the absolute readout is encoded there. A final -1 readout on ReLU(1)=1 gives logit -1, whereas encoding that readout as another Network.layer gives 0.',
'minimal_repair':'Specify one backbone-plus-affine-output model and define its actual two split head functions, including readout bias. Prove recovery, zero-shift actual head derivatives, canonical readout absolute-mass identity, and both partial invariants for that model using existing run_zero_actual and derivative lemmas. In the source set final M+=I and M-=0 where uniform recursion notation is used, and exclude a final minimum/Q source for the ungated readout.',
'not_a_counterexample_to_lean':True,'metadata_verdict':'Existing affine wrapper substantially reduces the work, but does not by itself make all source-linked fully gated head statements statements about affine logits.'
},
{
'id':'HM-03','severity':'medium','classification':'verified_source_counterexample','title':'Saliency prose drops the suffix factor in the intermediate shifted bulk',
'source_locations':[T('05_saliency','the subtracted direction')],
'lean_locations':[L('StabilizedBackward','theorem MaskedTrace.stabilized_bulk'),L('StabilizedBackward','theorem MaskedTrace.pull_sum')],
'evidence':'For one active scalar layer W=1, terminal g seed (1,0), and output shift alpha=1/4, the incoming shifted seed is (3/4,-1/4). Its pullback sum is 1/2, whereas W_abs=1. Checks.lean verifies these exact rational identities and inequality. The source sentence identifies the intermediate sum with W_abs; the correct quantity is the suffix product of (1-2 alpha) times W_abs. Chapter 03 equation claim_bulk and the Lean implementation already have the correct factor.',
'minimal_repair':'Replace the asserted equality with intermediate_bulk(l)=product_{i=l+1..L}(1-2 alpha_i) W_abs[l], with the corresponding terminal convention for an affine readout. Preserve the statement that this remains independent of activation patterns.',
'not_a_counterexample_to_lean':True
},
{
'id':'HM-04','severity':'medium','classification':'definite_metadata_target_mismatch','title':'The linear-chunk source link advertises an affine theorem but points to an activated theorem',
'source_locations':[T('03_decompositions','\\begin{lemmaenv}[Non-negative linear chunks'),loc('formalization/coverage_map.json','"lem:linear_chunk"'),loc('formalization/tex_links.json','"lem:linear_chunk"')],
'lean_locations':[L('Core','theorem pre_difference'),L('Network','theorem layer_difference'),L('OriginalTrace','theorem preactivation_difference')],
'evidence':'The source lemma asserts arbitrary affine pair recovery, nonnegative outputs, affine dependence, convexity and monotonicity. tex_links points to pre_difference, which is scalar, bias-free algebra. coverage_map additionally cites layer_difference, whose conclusion is ReLU((Wp-Wn)(p-n)+(bp-bn)), because its positive branch has a max. It is not the source affine operation. At A=1,c=-1,p=n=0 the source affine difference is -1 while the cited activated difference is 0 (exact arithmetic checked in Checks.lean). A genuinely suitable vector/bias algebraic identity preactivation_difference already exists but is not the cited theorem, and the advertised property bundle is not packaged for this chunk.',
'minimal_repair':'Link to a source-facing affine-chunk theorem based on preactivation_difference and explicit nonnegative sign-split parameters, bundling recovery, nonnegativity, affine/convex and monotone properties. Until then mark this lemma component coverage, not an affine-network variant justified by layer_difference.',
'not_a_counterexample_to_lean':True
},
{
'id':'HM-05','severity':'medium','classification':'definite_formal_model_gap','title':'CNN correctness does not model the permitted winner-takes-all pooling pass',
'source_locations':[T('03_decompositions','winner-takes-all'),T('03_decompositions','If neither winner-takes-all')],
'lean_locations':[L('Chunks','theorem winner_pool_correct'),L('MultiplicativeSplit','def SignedExpr.split'),L('Circuit','def Circuit.split'),L('CircuitStatements','theorem Circuit.cnn_split_correct')],
'evidence':'Circuit.split always uses SignedExpr.split. Its maximum constructor is the convex split (max(p+r,q+n),n+r), not shared-winner forwarding. winner_pool_correct is exactly p j - n j = (p-n) j with arbitrary j; its type contains neither an argmax condition nor equality to the pool maximum. Thus it is not a correctness proof of the winner selection and there is no graph interpreter for the source optional WTA pass. For p=(10,2), n=(9,0), source WTA produces (2,0), whereas the encoded convex split produces (11,9). Both differences are 2, but these are different stream functions. The existing global center Bool also represents all nodes recentered or none, rather than an independently chosen per-node policy.',
'minimal_repair':'Add an explicit pooling rule and a chosen-winner certificate/maximizer theorem, then extend the graph semantics and all-node recovery. Retain convexity only for the convex pooling rule without input-dependent recentering. If arbitrary per-node recentering is intended, parameterize the policy per node.',
'not_a_counterexample_to_lean':True,'metadata_verdict':'The variant scope describes the encoded DAG, but does not justify the whole optional-pooling source statement.'
},
{
'id':'HM-06','severity':'medium','classification':'definite_component_only_coverage','title':'Max-pool proposition has only its difference identity linked',
'source_locations':[T('03_decompositions','\\begin{proposition}[Correctness of gated max-pooling]'),loc('formalization/coverage_map.json','"prop:maxpool_correct"')],
'lean_locations':[L('Chunks','theorem maxpool_correct'),L('CircuitStatements','theorem Circuit.cnn_stream_properties')],
'evidence':'maxpool_correct proves the finite nonempty sup difference identity. It does not state the source proposition\'s nonnegative-output, convexity or coordinatewise monotonicity conclusions. Generic additive Circuit properties exist, but no theorem identifies the source finite pool pair with a particular Circuit or directly instantiates those properties for the exact sup/erase-sum functions. The metadata scope itself says exact finite nonempty identity, while status is formalized_variant and the source badge labels the whole proposition.',
'minimal_repair':'Package the direct finite-pool positivity/convexity/monotonicity proof, or prove the precise finite-pool-to-Circuit bridge and specialize the generic results; otherwise label component coverage.',
'not_a_counterexample_to_lean':True
},
{
'id':'HM-07','severity':'low','classification':'definite_boundary_convention_mismatch','title':'Extracted gates choose the opposite branch at zero from the printed mask convention',
'source_locations':[T('03_decompositions','Here $M^{(l,+)}'),T('05_saliency','Write $M^{(l,+)}')],
'lean_locations':[L('OriginalTrace','def originalGate'),L('MaskedTrace','def Network.trace')],
'evidence':'The source defines M+ by z>=0 and M- by z<0. Lean originalGate uses decide (0<z), and trace chooses positive max branch only for a strict positive difference. At z=0 the source mask is active and the Lean extracted mask inactive. Checks.lean verifies the Lean gate is false for a scalar unit weight at zero. The derivative theorems requiring Strict are unaffected. The discrepancy matters when claiming this exact extracted-mask algorithm matches the source at ties: for scalar ReLU at zero, zero-shift g balanced selected sensitivity is +1/2 under the source active tie and -1/2 under the Lean inactive tie.',
'minimal_repair':'Align the printed and executable tie convention, or parameterize tie choices and state the agreement theorem only away from ties. Do not interpret either selected value as the ordinary derivative of ReLU at zero.',
'not_a_counterexample_to_lean':True
},
{
'id':'HM-08','severity':'low','classification':'verified_source_convention_error','title':'The eta-zero remark uses sign parts that cannot be canonical and overstates later preactivation convexity',
'source_locations':[T('03_decompositions','\\begin{remark}[On the $\\eta = 0$')],
'lean_locations':[L('OriginalTrace','def Network.Canonical'),L('Decomposition','def mixPair')],
'evidence':'The source gives scalar W+=2,W-=1 as an example under its canonical sign-split convention; no real scalar weight has those canonical parts, since both parts cannot be strictly positive. The same paragraph says eta-zero preactivations are convex from layer 1 onward, which does not follow: with scalar W=1,b=1 and canonical input split, eta-zero negative output is h(x)=min(max(x,0)+1,max(-x,0)). Its values at x=-2,0,-1 are 1,0,1, violating convexity at their midpoint. A subsequent positive affine map can inherit this nonconvexity. The formal mixing recovery theorem does not assert this convexity and is unaffected.',
'minimal_repair':'Use a canonical example such as W=1,b=1 and state that the first preactivations are convex, while later eta-zero streams and preactivations need not be convex. Keep the arithmetic recovery result separate.',
'not_a_counterexample_to_lean':True
}
]
# Inventory every declaration whose complete source module was read. This is source inspection,
# not an assertion that all were independently recompiled in this audit.
decls=[]
for path in sorted(Path('formalization/HiddenMonotonicity').glob('*.lean')):
    ns=[]
    for line,text in enumerate(path.read_text().splitlines(),1):
        m=re.match(r'namespace\s+(\S+)',text)
        if m:ns.append(m.group(1));continue
        if re.match(r'end(?:\s|$)',text):
            if ns:ns.pop()
            continue
        m=re.match(r'(?:@\[[^]]*\]\s*)?(?:noncomputable\s+)?(theorem|def|abbrev|inductive|structure)\s+([^\s:{]+)',text)
        if m:decls.append({'name':'.'.join(ns+[m.group(2)]),'kind':m.group(1),'file':str(path),'line':line})
examples=[i+1 for i,s in enumerate((evidence/'ExactBackwardTypes.lean').read_text().splitlines()) if s.startswith('example :')]
claims=[]
for name,idx,verdict in [
('Network.stabilized_backward_absolute_Q_closed_form',0,'Faithful corrected shifted formula on strict original gates and canonical weights; actual Q derivatives, arbitrary finite widths/biases and real layer shifts. Algorithmic shifted quantities are not asserted to be actual derivatives of recentered heads.'),
('Network.plain_head_gradient_formulas',1,'Actual full Frechet derivatives of balanced-lift projection heads, including both signs and factor 1/2. Strict-gate and fully activated-backbone scope are explicit.'),
('Network.backward_partial_invariants',2,'Both separate cross-head partial identities and actual original derivative. No arbitrary recurrence is assumed.'),
('Network.stabilized_backward_invariant',3,'The balanced difference is the actual derivative of the row projection of original eval at strict gates.'),
('Network.affine_readout_closed_form',4,'Correct terminal-seed formula for arbitrary signed affine readout algebra; the separate forward affine-head model and canonical absolute-readout bridge remain unbundled.')]:
    claims.append({'declaration':'HiddenMonotonicity.'+name,'expected_type_receipt':{'file':str(evidence/'ExactBackwardTypes.lean'),'line':examples[idx]},'typecheck_exit':0,'axioms':['propext','Classical.choice','Quot.sound'],'model_correspondence_verdict':verdict})
report={
'audit':'Independent adversarial Hidden Monotonicity source-to-Lean audit',
'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
'reviewer':'/root/attack_hidden',
'verdict':'The inspected backward, Q-source, split-recovery and DAG statements are genuine theorems of their stated Lean models; no false Lean statement, accidental auto-bound premise or forbidden axiom was found in the exact-checked headline subset. Complete source coverage and a caveat-free all-thesis claim are not established. Source errors, model gaps and scope restrictions are separated below.',
'findings':findings,
'positive_checks':[
'Canonical weight requirement is unfolded: wp=max(wp-wn,0), wn=max(-(wp-wn),0); absCLM_eq_absoluteMap proves the absolute-weight bridge for the entire variable-width tail. Bias canonicality is not needed for backward identities; nonnegative parameter hypotheses are separate for forward positivity.',
'Balanced lift is (x/2,-x/2); unified is (partialPlus-partialMinus)/2. Both partial invariants and the correct factor 2 in their unbalanced difference are present.',
'Stabilized sensitivities are explicitly computed by pull then equal shift at each layer, including output. The correction uses the suffix bulk above the transition; the local shift cancels. bulkCoefficient_product proves the finite product.',
'Actual split and original Frechet derivatives are proved from strict branch derivatives. zero_shift_actual and local_sensitivities_correct connect the implemented unshifted recurrence to the actual head functions. plain_head_gradient_formulas provides full Vec-to-real derivatives, not only a radial/directional test.',
'Every Q retains the original nonlinear prefix with its biases, uses one min at the designated layer, and has a bias-free linear absolute-weight tail. qSources_have_derivatives computes genuine Q Frechet derivatives; qSources_sum identifies the exact finite sum.',
'Current archived proofs.tex and thesis chapter 03 already use corrected factor-1/2, suffix indices, and explicit linear-tail Q definition. Historical counterexample declarations do not refute the current corrected source statements.',
'Circuit is an actual topologically ordered graph with access to earlier shared nodes. Split correctness holds at every node; nonnegative outputs are proved with optional global min recentering. Convexity/monotonicity excludes products and recentering where needed.',
'Multiplicative representations are exact on nonnegative split inputs. Ordinary MvPolynomial witnesses have actual nonnegative coefficients, natural exponents and a proved nonempty finite leaf list. foldMax starts at zero harmlessly because every represented polynomial is nonnegative on that domain.',
'The smooth-curvature source modules were read: their primitive and tilt definitions are genuine integrals and suprema, not definitions that assume decomposition. This audit does not supply an independent exact-type receipt for all smooth results.'
],
'honestly_declared_remaining_scope':[
{'item':'Fixed-rank/bounded-total-degree linear-size theorem','source':'arxive/hiddenMonotonicity/appendix/maxout_networks.tex:thm:main','status':'coverage_map thm:main and claim:main_correct explicitly partial; no graph-size/rank-count theorem found. This is not concealed over-credit.'},
{'item':'Concrete tensor convolution flattening','status':'No tensor/convolution index equivalence proved; prop:conv_correct is explicitly partial. Generic affine operations express flattened values, but application-specific indexing is outside the proof.'},
{'item':'Convexity under arbitrary convex input splittings for eta=1','status':'coverage_map marks mixing_convex_extreme partial and explains the absent composition theorem.'},
{'item':'Forward recentering and detached backward differentiation','status':'Current source explicitly distinguishes fixed/constant shifts, detached input-dependent shifts and ordinary differentiated recentered heads. No theorem falsely equates the latter with shifted algorithmic sensitivities.'}
],
'exact_checked_claims':claims,
'checks':{
'lean':{'command':'cd formalization && lake env lean .lake/diagnostics/attack_hidden/Checks.lean; lake env lean .lake/diagnostics/attack_hidden/ExactBackwardTypes.lean','receipts':[str(evidence/'checks.log'),str(evidence/'exact-types.log')],'exit_codes':[0,0],'status':'Diagnostic exact-type/axiom receipts using the existing import cache; not a clean committed-closure rebuild.'},
'rational':json.loads((evidence/'rational_audit.json').read_text()),
'rational_producer':str(evidence/'rational_audit.py'),
'rational_cases':str(evidence/'rational_cases.json'),
'independence':'Rational experiments calculate actual plain head derivatives by forward-mode dual numbers, and Q sources through independent original prefixes/minimum/linear tails; shifted partials use a separate backward pass. Arithmetic is Fraction exact, not floating point.',
'reproducibility':'From repository root: python3 reports/evidence/attack_hidden/rational_audit.py. For Lean, copy the two evidence .lean files to formalization/.lake/diagnostics/attack_hidden/ and run the recorded commands with the declared Lean/mathlib v4.35.0 environment.'
},
'skills_read':[str(p) for p in sorted(Path('skills/upstream-planar-features').glob('*/SKILL.md'))],
'source_declarations_reviewed':decls,
'limitations':['No production source, shared .olean or build cache was mutated. Only audit scratch and the explicitly requested reports/evidence paths were written.','No external literature was needed: the supplied local manuscript and source were the comparison authority.','Finite experiments do not establish universal correctness. Kernel receipts are limited to explicitly imported and exact-checked declarations.','No end-to-end PyTorch converter, floating-point stabilization implementation, runtime complexity, or clean clone reproducibility was verified.']
}
Path('reports/adversarial-hidden.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
paths=list(evidence.glob('*'))+list(Path('formalization/HiddenMonotonicity').glob('*.lean'))+[Path('formalization/coverage_map.json'),Path('formalization/tex_links.json'),Path('formalization/lean-toolchain'),Path('formalization/lakefile.toml'),Path('tex/chapters/03_decompositions.tex'),Path('tex/chapters/05_saliency.tex')]+list(Path('arxive/hiddenMonotonicity/sections').glob('*.tex'))+list(Path('arxive/hiddenMonotonicity/appendix').glob('*.tex'))
hashes={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths) if p.is_file() and p.name!='sha256.json'}
(evidence/'sha256.json').write_text(json.dumps(hashes,indent=2)+'\n')
print(json.dumps({'report':'reports/adversarial-hidden.json','findings':len(findings),'source_declarations_reviewed':len(decls),'sha256_manifest':str(evidence/'sha256.json')}))
