#!/usr/bin/env python3
"""Complete active-source label coverage verdicts, against the saved source snapshot."""
from pathlib import Path
import json,hashlib,importlib.util,collections
ROOT=Path(__file__).resolve().parents[3];OUT=Path(__file__).resolve().parent
D=json.loads((OUT/'inventory.json').read_text());P=json.loads((ROOT/'reports/additional-tex-links.json').read_text());R=json.loads((OUT/'mapping-receipts.json').read_text());C=json.loads((OUT/'all-contracts.json').read_text())
notes={}
def note(labels,status,reason,candidates=[]):
 for l in labels.split():notes[l]={'status':status,'reason':reason,'candidate_declarations_not_promoted':candidates}
note('ptnb:lem:noisy-gate-dual ptnb:eq:noisy-gate-defn ptnb:eq:noisy-gate-regulariser ptnb:eq:noisy-gate-objective ptnb:eq:noisy-gate-optimum ptnb:eq:noisy-gate-deriv ptnb:eq:noisy-gate-marginal','not_formalized','Gaussian/probit inverse-CDF regularizer and expected noisy ReLU identity have no reviewed matching development. Binary entropy/sigmoid is a different function, not a specialization.')
note('ptnb:thm:attention','not_formalized_as_stated','Full reference-attention subgame SPNE plus occupation bridge is not assembled. Active local KL optimum and epsilon-positive conditioned effective-map recurrence are separately proved.')
note('ptnb:eq:conditioned-alpha ptnb:eq:conditioned-geom-kernel ptnb:eq:conditioned-bc-kernel ptnb:eq:ordinary-bc ptnb:eq:conditioned-h2 ptnb:eq:conditioned-per-pixel-h2','reports_only_draft_not_promoted','ConditionedTrajectory has a compiling reports-only composition draft, but no frozen production module or approved contract receipt. Do not cite it as a completed public proof.')
note('eq:forward_recursion eq:network_function eq:original_forward_pass eq:stream_functions eq:stream_recursion','model_definition_not_linked','Shared Network.eval/split and affineHeads/affineLogit encode the backbone and ungated scalar readout. No single reviewed definition contract here states the displayed indexed vector recursion including every terminal case.', ['HiddenMonotonicity.Network.eval','HiddenMonotonicity.Network.affineLogit','HiddenMonotonicity.Network.affineHeads'])
note('eq:max_as_relu','existing_construction_not_exact_display_contract','The ReLU compiler constructs binary maxima, but the literal symmetric half-sum/absolute-value chain in this equation has no inspected exact contract. Do not link the overall compiler as if it directly asserted that scalar chain.')
note('eq:maxout_unit eq:maxout_layer','model_definition_not_linked','Finite max-affine polynomials and source Maxout gate evaluator exist, but no separately reviewed definition/equality contract for this exact full displayed layer expression.')
note('eq:mdp_value','model_representation_scope','Bellman policyValue has a checked convergent Markov-operator reward series. An explicit infinite trajectory measure/expectation identification is not present in that target.')
note('eq:structural_discount eq:rng_kernel eq:rng_cont_value','existing_model_or_helper_needs_exact_contract','ReLUNetGame rowDiscount/continuation encode these local transition expressions. The selected end-to-end game contract assumes nonzero fan-in; no additional local definition/equality contract was admitted in this batch.')
note('eq:tropical_operations','notation_only','Max-plus operations are notation for maximum and addition; a generic polynomial theorem should not be presented as a proof of notation.')
note('eq:halfspace_description eq:prototype_evaluation','existing_geometry_components_no_single_display_contract','Compact support separation/extreme-point attainment and uniqueness are checked. The literal all-halfspaces set equality or vertex-set maximum needs an exact source-facing equation contract; no unrelated gradient theorem is substituted.')
note('eq:input_split_convention ptnb:eq:input-split-convention','definition_or_hypothesis','Source permits any nonnegative input pair with difference x. Canonical split preprocessing exists, but does not define every permitted split; no single canonical-only link is used.')
note('eq:validity_condition','definition_or_hypothesis','This is the assumption defining a valid pair activation/decomposition, not an unconditional recovery theorem. ValidPairActivation exists but has no added definition contract in this batch.')
note('ptnb:eq:bellman','game_encoding_scope','The source uses player-dependent action advantages. LayeredGames supplies a max/min Bellman game; no exact contract for this displayed two-player state formula was reviewed.')
note('ptnb:eq:q-value ptnb:eq:routing-linear-action ptnb:eq:optimal-linear ptnb:eq:routing-linear-value ptnb:eq:routing-activation-continue ptnb:eq:routing-forward-linear ptnb:eq:routing-forward-continue','existing_game_components_no_exact_display_bundle','Extended-log sourceValue, reported coordinates, tree routes and anchor forward values are checked separately. The full source state/sign/outside-action formula is not the literal conclusion of one admitted contract; no replacement by a generic entropy inequality.')
note('ptnb:eq:soft-bellman ptnb:eq:gibbs-policy ptnb:eq:routing-spne-linear ptnb:eq:routing-gibbs-general-tau ptnb:eq:rg-T','existing_game_components_no_exact_display_bundle','Finite real-score Gibbs optimum and extended zero-mass routing are proved. A checked source state-to-score bridge plus exact generalized-temperature policy expression is needed for this entire contextual equation.')
note('ptnb:eq:adf-kernel-stop ptnb:eq:adf-kernel ptnb:eq:adf-T','existing_model_or_helper_needs_exact_contract','StoppingBoundary implements cemetery-aware transitions, including zero fan-in, and proves normalization/gradient identities. This precise conditional transition definition was not added as an exact contract.')
note('ptnb:eq:adf-q-bellman ptnb:eq:adf-q-stop ptnb:eq:adf-q-cont ptnb:eq:adf-v-terminal ptnb:eq:adf-v-active ptnb:eq:adf-advantage ptnb:eq:adf-spne-values','source_player_bookkeeping_bridge_gap','Stopping ordinary zero-sum game values and stopping pairs are proved separately. The complete arbitrary-profile player-specific stopping payoff-to-decomposition bridge is not supplied by those two theorems. The new SoftplusGame bridge is for positive temperature, not a proof of this hard game by substitution.')
note('ptnb:eq:adf-spne-policy','existing_relevant_restricted_model','The strict-positive optimalStrategy is certified for the layered ReLUNetGame with NonzeroRows. This source section has a broader graph/player-bookkeeping game; do not silently identify the models.')
note('ptnb:eq:routing-sigma-def ptnb:eq:routing-Gamma-pair ptnb:eq:routing-edge-discount ptnb:eq:routing-discount ptnb:eq:routing-per-state-recursion ptnb:eq:lrp-eps-policy','existing_model_or_helper_needs_exact_contract','Literal routing denominator, sign-path discount/occupation and anchor probability components exist. A whole displayed-source formula contract covering the state/sign conventions and all listed bias/outside cases has not been added.')
note('ptnb:eq:routing-add-max','not_formalized_as_full_source_game','The actual routing Network proof is layered. A source residual/addition/maxpool routing-game compiler/SPNE bridge is not in the frozen reviewed set.')
note('ptnb:eq:attn-V-forward ptnb:eq:attn-AV-forward ptnb:eq:attn-composite-weight ptnb:eq:attn-Z-def ptnb:eq:attn-z-def','existing_conditioned_affine_model_needs_exact_display_contract','AttentionBackward defines the fixed-A signed Value projection and flattened effective matrix. The derivative contract does not assert every displayed tensor identity/normalizer. A dedicated exact definition/identity receipt is needed.')
note('ptnb:eq:attn-target-rule ptnb:eq:attn-target-input-via-V ptnb:eq:attn-target-input ptnb:eq:attn-V-routing-policy ptnb:eq:attn-Gamma-X ptnb:eq:attn-ab-recovery ptnb:eq:attn-Gamma-O ptnb:eq:attn-Gamma-V-corollary ptnb:eq:attn-Gamma-X-recursion','attention_game_and_zero_support_scope_gap','The reviewed AttentionBackward recovery uses positive epsilon and a conditioned effective affine map; the source displays epsilon-free per-key/per-channel SPNE occupations and grouped Value relevance. Active local AttentionReference optimum does not prove these global/full-chain formulas.')
note('ptnb:eq:risk-attn-policy ptnb:eq:risk-attn-policy-softmax ptnb:eq:equivariant-average','method_definition_not_formalized','These proposed risk-score/equivariant saliency method definitions have no inspected Lean model; entropy optimum alone would be an unrelated proof of their complete method claim.')
note('eq:ig_counterexample','example_not_formalized','Explicit IG/split-sensitivity example has no reviewed Lean consumer establishing the stated surrounding interpretation.')
note('eq:layercam eq:splitcam_stream eq:splitcam_combined eq:gamma_contribution eq:lrp_gamma_rule eq:splitlrp_combined eq:splitgrad','method_definition_not_formalized','Application-level CAM/LRP-gamma/SplitGrad construction is not implemented by the mathematical backbone contracts. Alpha-beta routing is a different redistribution rule.')
note('ptnb:eq:cemetery-absorbing ptnb:eq:rg-T-act ptnb:eq:rg-T-pixel','existing_model_or_helper_needs_exact_contract','Boundary transition modules model these probabilities with fixed endpoint conventions. A new exact definition/equality receipt is needed to link this complete source display.')
note('ptnb:eq:lmp-alpha ptnb:eq:lmp-alpha-boundary ptnb:eq:lmp-alpha-recursion','marginal_model_not_packaged','Generic transport and trajectory endpoint-fibre constructions exist; source prefix marginal identity/recursion was not given an admitted exact contract. The reports-only trajectory draft should not be used as a completed public proof.')
note('ptnb:eq:geom-kernel ptnb:eq:geom-rowsum','notation_only','The geometric kernel and its row sum are literal finite expressions in checked Games theorems, but no named definition contract for these source names is required to justify them.')
note('ptnb:eq:ordinary-h2','derived_finite_sum_bookkeeping','The per-pixel full total is now exactly linked; subtracting the one cemetery terminal is elementary finite-sum bookkeeping, with no dedicated contract admitted here.')
note('ptnb:eq:survival-function ptnb:eq:survival-boundary ptnb:eq:survival-mass','survival_representation_scope','Actual ordinary-kernel backwardDP survival and path mass are checked, but this entire display also names conditional-probability events, layer cemetery zero, endpoint marginals and 1-minus-cemetery. Those explicit representation equalities are not all in the core contract.')
partial={
 'thm:shapley_bellman':'Formal model is layered with a common nonempty action type; arbitrary finite DAG-to-layered encoding is not in this contract.',
 'thm:relu_net_game_value':'Actual normalized game/readout proof has nonzero-fan-in assumptions; source permits cemetery conventions beyond that primary target.',
 'prop:stream_properties':'Existing primary target proves monotonicity only. Convexity is separately proved by Network.convex and affine_heads_convex_input; metadata must not claim monotone itself proves convexity.',
 'thm:shift_forward':'Primary Network.shift covers hidden split backbone. Final affine common shift follows by the actual affineHeads definition, but is not stated in this target.',
 'thm:delta_connection':'Primary target is selected-row mass at all inputs; classical sensitivity interpretation needs the separately proved affine_head_derivative correspondence on the source strict cells.',
 'thm:cnn_split_correct':'Actual scalar DAG recovery/convex pooling, tensor convolution bridge and size components exist. A single source CNN architecture/compiler bundle remains unassembled.',
 'ptnb:thm:gradient':'Primary target has strict cells and nonzero fan-in. New StoppingBoundary removes nonzero fan-in and DAGIntermediate covers selected general graph occupations; the source global SPNE model identification is separate.',
 'ptnb:thm:lrp-recovery':'Old positive-epsilon/gated recovery metadata is stale: RoutingSupport now proves literal source recurrence and epsilon-zero algebra for supported/output seeds. Global source routing-game assembly remains distinct.',
 'ptnb:thm:forward-stopping':'Normalized ordinary game SPNE and stopping pairs are separately proved; arbitrary-profile player-bookkeeping and full graph model correspondence remain.',
 'ptnb:thm:deriv-occ':'Actual strict/regular shared-DAG derivative/occupation identity proved, with ordered finite-pool adapter. Source global SPNE identification is not part of this selected-policy derivative contract.',
 'ptnb:thm:routing-forward':'Actual layered routing game SPNE at all positive temperatures; no general residual/maxpool routing graph compiler or exhaustive policy uniqueness classification.',
 'ptnb:thm:softplus-forward':'Now full arbitrary-profile layered SPNE/player-value result. Source residual/maxpool graph extension remains pending a separately frozen batch.',
 'ptnb:thm:softplus-gradient':'Now actual layered all-SPNE intermediate gradient and affine output recovery; source full Circuit extension remains pending.',
 'ptnb:prop:attn-value-policy':'Active positive-total optimizer includes zero entries; all-zero active value separately bottom. Inactive-player bottom coordinate is not a field of AttentionReference.',
 'ptnb:thm:attn-ab-recovery':'Positive-epsilon effective-affine recurrence is checked; source epsilon-free grouped attention SPNE occupation formula is stronger.',
 'ptnb:lem:bc-monotone':'Current contract is one-step geometric row substochasticity, not the literal full-prefix overlap monotonicity chain. Reports-only ConditionedTrajectory draft is not promoted.',
 'ptnb:lem:hellinger-backward-correctness':'Trajectory overlap equals backwardDP is proved. Source algorithm also computes per-state forward masses and per-pixel output, so the complete algorithm correctness bundle is not this single contract.',
 'ptnb:thm:conditioned-survival':'Core zero-inclusive conditioned path law is now proved. Source intermediate marginals/geometric conditioning/BC/Hellinger composition remains a reports-only draft.',
 'ptnb:thm:rand-adf':'Conditional-expectation kernel theorem assumes the conditional alive-probability bound; the concrete randomized-weight model bridge is not derived.',
 'ptnb:thm:rand-routing':'Source states a deterministic per-row bound. Existing linked theorem is a conditional-expectation full-depth result; deterministic specialization is available mathematically but not a literal source-facing contract.'}
for k,v in partial.items():notes[k]={'status':'formalized_components_or_restricted_model','reason':v,'candidate_declarations_not_promoted':[]}
# Existing proof components with exact reviewed types; avoid calling these unformalized.
companions={
 'prop:stream_properties':['HiddenMonotonicity.Network.convex','HiddenMonotonicity.Network.affine_heads_convex_input'],
 'prop:validity_recovery':['HiddenMonotonicity.preactivation_difference','HiddenMonotonicity.linear_chunk_properties'],
 'cor:dc_split_endpoint':['HiddenMonotonicity.Network.mixing_one_convex_input','HiddenMonotonicity.Network.affine_heads_recovery'],
 'thm:delta_connection':['HiddenMonotonicity.Network.affine_head_derivative_of_differentiable'],
 'prop:sensitivity_mass':['HiddenMonotonicity.Network.affine_head_derivative_of_differentiable'],
 'ptnb:thm:gradient':['Thesis.StoppingBoundary.strict_gradient_occupation','Thesis.StoppingDAG.intermediate_circuit_derivative_occupation'],
 'ptnb:thm:lrp-recovery':['Thesis.RoutingSupport.source_alpha_beta_output_seed','Thesis.RoutingSupport.source_affine_output_lrp'],
 'ptnb:lem:bc-chain-rule':['Thesis.Games.trajectory_overlap_eq_DP'],
 'ptnb:lem:alive-mismatch':['Thesis.Randomization.thesis_alive_mismatch_full']}
rows=[]
for r in D['records']:
 for label in r['labels']:
  existing=D['links'].get(label);proposed=P.get(label)
  item={'label':label,'file':r['file'],'line':r['line'],'environment':r['environment'],'kind':r['kind'],'source_text_sha256':hashlib.sha256(r['text'].encode()).hexdigest(),'source_text':r['text'],'existing_link':existing,'proposed_link':proposed}
  if label in notes:item.update(notes[label])
  elif proposed:item.update(status=R[label]['verdict'],reason=R[label]['correspondence'])
  elif existing:item.update(status='existing_relevant_checked_link',reason=existing.get('scope','Direct reviewed target already linked; exact contract is retained.'))
  elif r['kind']=='statement' and any(l in P or l in D['links'] for l in r['labels']):
   item.update(status='same_environment_alias',reason='Alias of the already-linked statement '+next(l for l in r['labels'] if l in P or l in D['links'])+'; no duplicate heading badge or unrelated declaration is needed.')
  elif r['kind']=='statement' and r['environment'] in ['definition','remark']:
   item.update(status='definition_or_expository_remark_unlinked',reason='No new full source correspondence is asserted for this expository/definition environment.')
  else:item.update(status='no_reviewed_mapping_located',reason='No faithful admitted exact contract identified; this is not a claim that the mathematics is false or absent from dependencies.')
  item['supporting_declarations']=R.get(label,{}).get('supporting_declarations',[])+companions.get(label,[])
  rows.append(item)
# Every numbered labeled equation is classified explicitly rather than left under a catch-all.
uncategorized=[r['label'] for r in rows if r['kind']=='equation' and r['status']=='no_reviewed_mapping_located']
assert not uncategorized,uncategorized
# Verify all target declarations physically exist and capture current frozen source hashes.
spec=importlib.util.spec_from_file_location('scanner',ROOT/'scripts/generate_lean_links.py');s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
source={};decls={}
for t in C.values():
 p=ROOT/'formalization'/Path(*t['module'].split('.')).with_suffix('.lean');rel=str(p.relative_to(ROOT))
 if rel not in source:
  source[rel]=hashlib.sha256(p.read_bytes()).hexdigest();decls.update(s.declarations(p.read_text(),rel))
receipts={}
for label,spec in P.items():
 name=spec['declaration'];assert name in decls,name
 t=C[name];receipts[label]={**R[label],'declaration':name,'module':t['module'],'kind':t.get('kind','theorem'),'expected_type':t['expected_type'],'expected_type_sha256':hashlib.sha256(t['expected_type'].encode()).hexdigest(),'source':decls[name],'module_sha256':source[decls[name]['path']],'contract_manifest':t['contract_manifest'],'scope':spec['scope']}
(OUT/'mapping-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
(OUT/'lean-source-sha256.json').write_text(json.dumps(source,indent=2)+'\n')
counts=collections.Counter(r['status'] for r in rows)
source_statements=[r for r in D['records'] if r['kind']=='statement' and r['environment'] not in ['remark','definition']]
report={
 'review_id':'attack_hidden/lean-link-coverage','status':'semantic_review_complete_exact_check_pending','scope':'Active thesis include closure only. Both archived papers informed correspondence, but their inactive duplicate labels are not new active thesis link targets. No production sources, manifests or TeX modified.',
 'source_inventory':'reports/evidence/lean-link-review/inventory.json','producer':'reports/evidence/lean-link-review/inventory.py','mapping_producer':'reports/evidence/lean-link-review/mappings.py','contract_authoring':'reports/evidence/lean-link-review/contracts.py','report_producer':'reports/evidence/lean-link-review/report.py',
 'counts':{'active_files':len(D['active_files']),'theorem_lemma_proposition_corollary_claim_observation_environments':len(source_statements),'definition_remark_environments':sum(r['environment'] in ['definition','remark'] for r in D['records']),'numbered_equation_environments':sum(r['kind']=='equation' for r in D['records']),'labeled_numbered_equation_environments':sum(r['kind']=='equation' and bool(r['labels']) for r in D['records']),'equation_labels':sum(r['kind']=='equation' for r in rows),'new_links':sum(k not in D['links'] for k in P),'updated_links':sum(k in D['links'] for k in P),'additional_exact_contracts':37,'verdict_counts':dict(counts)},
 'fragments':{'links':'reports/additional-tex-links.json','contracts':'reports/additional-link-expected-types.json','per_link_exact_receipts':'reports/evidence/lean-link-review/mapping-receipts.json'},
 'required_removals':[{'label':'ptnb:lem:noisy-gate-dual','declaration':'Thesis.Regularization.softplus_variational','reason':'Gaussian/probit dual is not binary entropy/softplus. This is a verified unrelated-link error; no replacement proposed.'}],
 'critical_scope_rules':['A definition link is kind=definition and certifies its checked type/body, not a new theorem.','A narrower model link must preserve its scope in the index; it cannot imply full source-statement coverage.','Every new equation points to an exact checked contract and carries a manual unfolding/specialization receipt.','No pending SoftplusCircuit or reports-only ConditionedTrajectory declaration is promoted.'],
 'stale_coverage_metadata':[
 {'labels':['ptnb:thm:softplus-forward','ptnb:thm:softplus-gradient'],'change':'Replace no-SPNE/positive-fan-in-only wording with the reviewed layered arbitrary-profile SPNE/player-value/occupation result; retain Circuit residual.'},
 {'labels':['ptnb:prop:attn-value-policy'],'change':'Strictly positive reference/contribution entries are no longer necessary for the active local optimum; AttentionReference handles zeros and all-zero bottom. Do not claim full attention game.'},
 {'labels':['ptnb:thm:conditioned-survival'],'change':'Remove obsolete global-positive-survival limitation for the core path law; retain missing intermediate marginal/statistics composition.'},
 {'labels':['ptnb:thm:lrp-recovery'],'change':'Literal source LRP and epsilon-zero supported/output-seed recovery now exist in RoutingSupport; global game bridge remains separate.'},
 {'labels':['ptnb:thm:gradient'],'change':'StoppingBoundary removes positive-fan-in necessity; actual DAG cut derivative/occupation is also proved. Existing old primary link is narrower.'},
 {'labels':['prop:stream_properties'],'change':'Network.monotone alone proves monotonicity; convexity is a separate existing exact contract, not missing mathematics.'},
 {'labels':['prop:maxpool_correct'],'change':'Current scope says both ConvexOn clauses and then No convexity asserted. Convex finitePool is convex; WTA winnerPool is a separate construction without that global claim.'},
 {'labels':['ptnb:thm:per-pixel'],'change':'Nonnegativity-only primary target cannot by itself establish the total identity; new exact formula/total contracts close this link gap.'},
 {'labels':['claim:main_correct'],'change':'Archived claim old size-unformalized metadata is stale: SplitDAGSize/MaxoutProductSize now count actual positive expression vertices/arcs. A source stepwise N_j replacement trace remains a distinct model assertion.'}
 ],
 'unformalized_or_unpromoted_source_statements':[{'label':k,**v} for k,v in notes.items() if k.startswith(('thm:','ptnb:thm:','ptnb:lem:')) and v['status'] in ['not_formalized','not_formalized_as_stated']],
 'restricted_or_unbundled_headline_statements':[{'label':k,**notes[k]} for k in partial],
 'unlabeled_numbered_math':[{'file':r['file'],'line':r['line'],'environment':r['environment'],'text':r['text']} for r in D['records'] if r['kind']=='equation' and not r['labels']],
 'all_active_label_verdicts':rows,
 'validation':{'new_exact_driver':'reports/evidence/lean-link-review/ExactTypes.lean','new_exact_log':'reports/evidence/lean-link-review/exact-types.log','source_hashes':'reports/evidence/lean-link-review/lean-source-sha256.json','all_contracts':'reports/evidence/lean-link-review/all-contracts.json','production_mutations':[]}
}
(ROOT/'reports/lean-link-coverage-review.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report['counts'],indent=2))
