"""Literal independently specified source contracts, not parsed Lean output."""
import importlib.util
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
prefix = '∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ)'
nn = '(hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i)'
hz = '(hz : 0 < ∑ i, mass reference contribution i)'
rows = [
 ('objective_eq_sourceValue', prefix + ' (p : Policy A) ' + nn + ',\n'
  'objective reference contribution p = sourceValue 1 (mass reference contribution) p',
  'Independent expected log-contribution minus reference KL, with separate impossible-action support guards, equals the extended Gibbs mass objective.'),
 ('valuePolicy_value', prefix + ' ' + nn + ' ' + hz + ',\n'
  'objective reference contribution (valuePolicy reference contribution hr hc hz) = '
  '(Real.log (∑ i, reference i * contribution i) : WithBot ℝ)',
  'Exact extended-log optimum at the literal reference-weighted mass ratio, allowing zero individual masses.'),
 ('valuePolicy_unique', prefix + ' (p : Policy A) ' + nn + ' ' + hz + ',\n'
  'objective reference contribution p = (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ↔ '
  'p.prob = (valuePolicy reference contribution hr hc hz).prob',
  'Unique maximizer over every finite simplex policy, including unsupported policies and simplex boundaries.'),
 ('zero_mass_value', prefix + ' (p : Policy A) ' + nn + '\n'
  '(hz : (∑ i, reference i * contribution i) = 0),\nobjective reference contribution p = ⊥',
  'Every candidate policy has genuine minus-infinity value for a zero-total-contribution stream; no real log-zero replacement.'),
 ('attention_value_routing', prefix + ' ' + nn + ' ' + hz + ',\n'
  'IsGreatest (Set.range (objective reference contribution)) '
  '(Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ∧\n'
  '(∀ p : Policy A, objective reference contribution p = '
  '(Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ↔ '
  'p.prob = (valuePolicy reference contribution hr hc hz).prob) ∧\n'
  '(∀ i, (valuePolicy reference contribution hr hc hz).prob i = '
  'reference i * contribution i / ∑ j, reference j * contribution j)',
  'Full active-player attention Value-routing optimum, uniqueness and exact policy, with nonnegative reference and Value contributions. Local subgame; global attention SPNE and occupations remain separate.')
]
targets = [dict(module='Thesis.AttentionReference', declaration='Thesis.AttentionReference.'+name,
 expected_type=typ, universes=['u'], open_namespaces=['Finset','Thesis.RoutingExtended','Thesis.AttentionReference'],
 review_id='ATTENTION-REFERENCE-'+name, review_evidence='reports/attention-reference-repairs.json', scope=scope)
 for name, typ, scope in rows]
(ROOT/'reports/attention-reference-expected-types.json').write_text(json.dumps({'targets':targets},indent=2)+'\n')
spec=importlib.util.spec_from_file_location('verify',ROOT/'formalization/scripts/verify.py')
verify=importlib.util.module_from_spec(spec);spec.loader.exec_module(verify)
out=Path(__file__).resolve().parent
(out/'ExactTypes.lean').write_text(verify.exact_driver({'public_root':'Thesis.AttentionReference','targets':targets},out))
