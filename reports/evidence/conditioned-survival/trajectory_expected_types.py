"""Independent literal intended contracts for the composed source clauses."""
import json
from pathlib import Path

targets = []
def target(name, typ, scope):
    targets.append({"module": "Thesis.ConditionedTrajectory",
        "declaration": "Thesis.ConditionedSurvival." + name,
        "expected_type": typ.strip(),
        "open_namespaces": ["Thesis.Games", "Thesis.ConditionedSurvival", "Thesis.Randomization"],
        "open_scopes": ["BigOperators"], "universes": [],
        "review_id": "SURVIVAL-COMPOSED-" + name,
        "review_evidence": "reports/conditioned-trajectory-repairs.md", "scope": scope})

target("timeMass_factorization", """
∀ {S : Type} [Fintype S] (N i : ℕ) (hi : i ≤ N)
(K : ℕ → S → S → ℝ) (s t : S),
timeMass N i K s t = prefixMass i K s t * survival N K i t
""", "Actual full-length path marginal factorization into the original time-i prefix occupation and backward future survival. Both marginals are independent literal sums on Games.Paths, using endpoint and stateAt. No representation or factorization hypothesis is assumed.")

target("conditioned_time_marginal", """
∀ {S : Type} [Fintype S] (N i : ℕ) (hi : i ≤ N)
(K : ℕ → S → S → ℝ) (hK : ∀ j s t, 0 ≤ K j s t)
(s : S) (hs : 0 < survival N K 0 s) (t : S),
timeMass N i (kernel K (survival N K)) s t =
prefixMass i K s t * survival N K i t / survival N K 0 s
""", "The source conditioned-alpha formula is proved for the actual time-i marginal of the full conditioned N-path distribution, including zero-potential states; only the initial survival mass must be positive.")

target("conditioned_geometric_kernel", """
∀ {S : Type} [Fintype S] (N : ℕ) (A B : ℕ → S → S → ℝ)
(hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
(i : ℕ) (s t : S),
Real.sqrt (kernel A (survival N A) i s t * kernel B (survival N B) i s t) =
Real.sqrt (A i s t * B i s t) *
Real.sqrt (survival N A (i+1) t * survival N B (i+1) t) /
Real.sqrt (survival N A i s * survival N B i s)
""", "Geometric-mean identity for the actual guarded conditioned kernels. At positive-potential states this is ordinary division; at zero denominator Lean's totalized quotient agrees with the explicit zero-row convention, whose unreachable support was proved separately.")

target("conditioned_survival_statistics", """
∀ {S : Type} [Fintype S] (N : ℕ) (A B : ℕ → S → S → ℝ)
(hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
(hArow : ∀ i s, ∑ t, A i s t ≤ 1) (hBrow : ∀ i s, ∑ t, B i s t ≤ 1)
(s : S) (hsA : 0 < survival N A 0 s) (hsB : 0 < survival N B 0 s),
(survival N A 0 s ≤ 1 ∧ survival N B 0 s ≤ 1) ∧
(∀ i ≤ N, ∀ t,
timeMass N i (kernel A (survival N A)) s t =
prefixMass i A s t * survival N A i t / survival N A 0 s ∧
timeMass N i (kernel B (survival N B)) s t =
prefixMass i B s t * survival N B i t / survival N B 0 s) ∧
(∀ i u v,
Real.sqrt (kernel A (survival N A) i u v * kernel B (survival N B) i u v) =
Real.sqrt (A i u v * B i u v) *
Real.sqrt (survival N A (i+1) v * survival N B (i+1) v) /
Real.sqrt (survival N A i u * survival N B i u)) ∧
(overlap (pathLaw N (kernel A (survival N A)) s)
(pathLaw N (kernel B (survival N B)) s) =
∑ path : Paths S N, pathLaw N (fun i u v => Real.sqrt
(kernel A (survival N A) i u v * kernel B (survival N B) i u v)) s path) ∧
(overlap (pathLaw N (kernel A (survival N A)) s)
(pathLaw N (kernel B (survival N B)) s) =
backwardDP N (fun i u v => Real.sqrt
(kernel A (survival N A) i u v * kernel B (survival N B) i u v)) (fun _ => 1) s) ∧
(overlap (pathLaw N (kernel A (survival N A)) s)
(pathLaw N (kernel B (survival N B)) s) =
ordinaryOverlap N A B s / Real.sqrt (survival N A 0 s * survival N B 0 s)) ∧
((1/2 : ℝ) * (∑ path : Paths S N,
(Real.sqrt (pathLaw N (kernel A (survival N A)) s path) -
Real.sqrt (pathLaw N (kernel B (survival N B)) s path))^2) =
1 - ordinaryOverlap N A B s / Real.sqrt (survival N A 0 s * survival N B 0 s))
""", "The remaining source conditioned-survival clauses are assembled: actual full-law layer marginals, conditioned geometric edges, overlap as a sum of actual geometric path products and as backwardDP, overlap normalized by computed initial survival masses, and the actual finite square-root Hellinger sum. Together with conditioned_survival in the frozen prerequisite this covers the requested ordinary-state survival, conditioning, pruning, marginal and comparison clauses. No strict positivity at intermediate states.")

target("trajectory_bc_monotone", """
∀ {S : Type} [Fintype S] (A B : ℕ → S → S → ℝ)
(hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
(hArow : ∀ i s, ∑ t, A i s t = 1) (hBrow : ∀ i s, ∑ t, B i s t = 1) (s : S),
overlap (pathLaw 0 A s) (pathLaw 0 B s) = 1 ∧
(∀ n, 0 ≤ overlap (pathLaw n A s) (pathLaw n B s) ∧
overlap (pathLaw n A s) (pathLaw n B s) ≤ 1) ∧
Antitone (fun n => overlap (pathLaw n A s) (pathLaw n B s)) ∧
Monotone (fun n => (1/2 : ℝ) * ∑ path : Paths S n,
(Real.sqrt (pathLaw n A s path) - Real.sqrt (pathLaw n B s path))^2) ∧
(∀ n, (1/2 : ℝ) * (∑ path : Paths S n,
(Real.sqrt (pathLaw n A s path) - Real.sqrt (pathLaw n B s path))^2) =
1 - overlap (pathLaw n A s) (pathLaw n B s)) ∧
(∀ n, overlap (pathLaw n A s) (pathLaw n B s) =
backwardDP n (fun i u v => Real.sqrt (A i u v * B i u v)) (fun _ => 1) s)
""", "Full source bc-monotone on actual row-stochastic Markov prefix path laws: overlap starts at one, stays in [0,1], is antitone at all depths, actual squared Hellinger is monotone, and every depth has the exact square-root sum and geometric-kernel DP identities. The common finite state space may include a cemetery; this is not an ordinary-only assertion about absorbing paths.")

root = Path(__file__).resolve().parents[3]
(root / "reports/conditioned-trajectory-expected-types.json").write_text(
    json.dumps({"targets": targets}, indent=2, ensure_ascii=False) + "\n")
