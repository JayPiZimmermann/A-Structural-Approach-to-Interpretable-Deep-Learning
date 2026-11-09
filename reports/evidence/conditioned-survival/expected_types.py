"""Independently specified public contracts; no Lean declaration inspection."""
import json
from pathlib import Path

targets = []
def target(name, typ, scope):
    targets.append({"module": "Thesis.ConditionedSurvival",
        "declaration": "Thesis.ConditionedSurvival." + name,
        "expected_type": typ.strip(),
        "open_namespaces": ["Thesis.Games", "Thesis.ConditionedSurvival"],
        "open_scopes": ["BigOperators"],
        "universes": [], "review_id": "SURVIVAL-ZERO-" + name,
        "review_evidence": "reports/conditioned-survival-repairs.md", "scope": scope})

target("weighted_path_identity", """
∀ {S : Type} [Fintype S] (n : ℕ) (K : ℕ → S → S → ℝ)
(h : ℕ → S → ℝ) (hK : ∀ i s t, 0 ≤ K i s t)
(hh : ∀ i s, 0 ≤ h i s)
(hrec : ∀ i < n, ∀ s, h i s = ∑ t, K i s t * h (i+1) t)
(s : S) (path : Paths S n),
pathLaw n (kernel K h) s path * h 0 s =
pathLaw n K s path * h n (endpoint n s path)
""", "Denominator-free finite-horizon Doob telescoping for nonnegative kernels and potentials satisfying the actual recurrence. No initial or intermediate strict positivity assumption; zero initial potential is included.")

target("path_zero_at_zero_potential", """
∀ {S : Type} (n : ℕ) (K : ℕ → S → S → ℝ)
(h : ℕ → S → ℝ) (hh : ∀ i s, 0 ≤ h i s)
(s : S) (hs : 0 < h 0 s) (path : Paths S n) (i : ℕ) (hi : i ≤ n)
(hz : h i (stateAt n s path i) = 0),
pathLaw n (kernel K h) s path = 0
""", "Actual full path state-at-index pruning: a zero-potential state visited anywhere on a path forces exactly zero conditioned path mass. Only the initial potential is assumed positive; no Fintype, recurrence or kernel-sign premise is required for this support fact.")

target("survival_recurrence", """
∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ)
(i : ℕ) (hi : i < N) (s : S),
survival N K i s = ∑ t, K i s t * survival N K (i+1) t
""", "The survival potential is defined by the original backwardDP with terminal payoff one; its finite-horizon recurrence is derived, not assumed.")

target("survival_eq_path_mass", """
∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ) (s : S),
survival N K 0 s = ∑ path : Paths S N, pathLaw N K s path
""", "Exact identification of the backward survival value with total mass of the original full surviving path sublaw.")

target("survival_zero_path", """
∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ)
(hK : ∀ i s t, 0 ≤ K i s t) (s : S) (hs : survival N K 0 s = 0)
(path : Paths S N), pathLaw N K s path = 0
""", "Zero initial survival implies every original full surviving trajectory has zero mass; no conditional probability at an impossible event is asserted.")

target("conditioned_survival", """
∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ)
(hK : ∀ i s t, 0 ≤ K i s t) (hrow : ∀ i s, ∑ t, K i s t ≤ 1)
(s : S) (hs : 0 < survival N K 0 s),
(∀ i t, 0 ≤ survival N K i t ∧ survival N K i t ≤ 1) ∧
(∀ t, survival N K N t = 1) ∧
(∀ i < N, ∀ u, survival N K i u = ∑ t, K i u t * survival N K (i+1) t) ∧
(survival N K 0 s = ∑ path : Paths S N, pathLaw N K s path) ∧
(∀ i < N, ∀ u, (∑ t, kernel K (survival N K) i u t) =
if 0 < survival N K i u then 1 else 0) ∧
(∀ i u t, survival N K (i+1) t = 0 → kernel K (survival N K) i u t = 0) ∧
(∀ path : Paths S N, pathLaw N (kernel K (survival N K)) s path =
pathLaw N K s path / survival N K 0 s) ∧
((∑ path : Paths S N, pathLaw N (kernel K (survival N K)) s path) = 1) ∧
(∀ (path : Paths S N) (i : ℕ), i ≤ N →
survival N K i (stateAt N s path i) = 0 →
pathLaw N (kernel K (survival N K)) s path = 0)
""", "Combined actual substochastic finite-kernel survival theorem: computed [0,1] potentials, terminal condition and recurrence, full path-mass identity, stochastic positive-potential rows and zero dead rows, zero-target support, exact normalized conditioned full path law, and explicit pruning of every path that visits a zero-potential state. Only initial survival must be positive. Does not by itself claim the marginal or Hellinger clauses of the wider source theorem.")

root = Path(__file__).resolve().parents[3]
(root / "reports/conditioned-survival-expected-types.json").write_text(
    json.dumps({"targets": targets}, indent=2, ensure_ascii=False) + "\n")
