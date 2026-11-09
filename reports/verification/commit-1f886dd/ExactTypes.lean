import All
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity
def _ThesisExpectedTypes.type_0 : Prop := (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical)
    (x : Vec n) (hx : net.Strict x) (α : ℕ → ℝ) (r : Row m),
    (∀ q ∈ net.absoluteQSources x α, HasFDerivAt q.value q.jacobian x) ∧
    unified ((net.originalTrace x).stabilized α r true) =
      (1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac -
        (sourceRows (net.absoluteQSources x α) r).sum) ∧
    unified ((net.originalTrace x).stabilized α r false) =
      (-1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac +
        (sourceRows (net.absoluteQSources x α) r).sum))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.QSources do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form"
#check @HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form
#print axioms _ThesisExactChecks.target_0

section
open HiddenMonotonicity
def _ThesisExpectedTypes.type_1 : Prop := (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical)
    (x : Vec n) (hx : net.Strict x) (r : Row m),
    HasFDerivAt (fun y : Vec n => r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).1)
      ((1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac-
        (sourceRows (net.absoluteQSources x (fun _ => 0)) r).sum)) x ∧
    HasFDerivAt (fun y : Vec n => r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).2)
      ((-1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac+
        (sourceRows (net.absoluteQSources x (fun _ => 0)) r).sum)) x)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @HiddenMonotonicity.Network.plain_head_gradient_formulas
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.plain_head_gradient_formulas
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.plain_head_gradient_formulas"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.plain_head_gradient_formulas | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.BackwardStatements do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.plain_head_gradient_formulas"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.plain_head_gradient_formulas: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.plain_head_gradient_formulas"
#check @HiddenMonotonicity.Network.plain_head_gradient_formulas
#print axioms _ThesisExactChecks.target_1

section
open HiddenMonotonicity
def _ThesisExpectedTypes.type_2 : Prop := (∀ {n m : ℕ} (net : Network n m) (x : Vec n) (hx : net.Strict x)
    (α : ℕ → ℝ) (r : Row m),
    HasFDerivAt (fun y => r (net.eval y)) (r.comp (net.originalTrace x).originalJac) x ∧
    ((net.originalTrace x).stabilized α r true).1-
      ((net.originalTrace x).stabilized α r false).1 = r.comp (net.originalTrace x).originalJac ∧
    ((net.originalTrace x).stabilized α r true).2-
      ((net.originalTrace x).stabilized α r false).2 = -(r.comp (net.originalTrace x).originalJac))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @HiddenMonotonicity.Network.backward_partial_invariants
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.backward_partial_invariants
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.backward_partial_invariants"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.backward_partial_invariants | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.BackwardStatements do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.backward_partial_invariants"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.backward_partial_invariants: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.backward_partial_invariants"
#check @HiddenMonotonicity.Network.backward_partial_invariants
#print axioms _ThesisExactChecks.target_2

section
open HiddenMonotonicity
def _ThesisExpectedTypes.type_3 : Prop := (∀ {n m : ℕ} (net : Network n m) (x : Vec n) (hx : net.Strict x)
    (α : ℕ → ℝ) (r : Row m),
    HasFDerivAt (fun y => r (net.eval y))
      (unified ((net.originalTrace x).stabilized α r true) -
       unified ((net.originalTrace x).stabilized α r false)) x)
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @HiddenMonotonicity.Network.stabilized_backward_invariant
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.stabilized_backward_invariant
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.stabilized_backward_invariant"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.stabilized_backward_invariant | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.QSources do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.stabilized_backward_invariant"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.stabilized_backward_invariant: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.stabilized_backward_invariant"
#check @HiddenMonotonicity.Network.stabilized_backward_invariant
#print axioms _ThesisExactChecks.target_3

section
open HiddenMonotonicity
def _ThesisExpectedTypes.type_4 : Prop := (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical)
    (x : Vec n) (hx : net.Strict x) (α : ℕ → ℝ)
    (rPlus rMinus : Row m) (β : ℝ),
    (∀ q ∈ net.absoluteQSources x α, HasFDerivAt q.value q.jacobian x) ∧
    unified ((net.originalTrace x).run α (affineReadoutSeed rPlus rMinus β true)) =
      (1/2 : ℝ) • ((rPlus-rMinus).comp (net.originalTrace x).originalJac -
        (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rPlus+rMinus))).sum) ∧
    unified ((net.originalTrace x).run α (affineReadoutSeed rPlus rMinus β false)) =
      (-1/2 : ℝ) • ((rPlus-rMinus).comp (net.originalTrace x).originalJac +
        (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rPlus+rMinus))).sum))
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4 := by exact @HiddenMonotonicity.Network.affine_readout_closed_form
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_readout_closed_form
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_readout_closed_form"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_readout_closed_form | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.AffineReadout do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_readout_closed_form"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_readout_closed_form: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_readout_closed_form"
#check @HiddenMonotonicity.Network.affine_readout_closed_form
#print axioms _ThesisExactChecks.target_4

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_5 : Prop := (∀ {n m k : ℕ} (net : Network n m) (σ : ℝ → ℝ)
    (hw : Foundations.PositiveWeights net) (hm : Monotone σ)
    (W : Matrix (Fin k) (Fin m) ℝ) (b : Fin k → ℝ) (hW : ∀ i j, 0 ≤ W i j),
    Monotone (fun x => W.mulVec (net.forwardWith σ x)+b))
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5 := by exact @Thesis.SourceFoundations.monotone_represents
end
run_cmd do
  let target ← getConstInfo `Thesis.SourceFoundations.monotone_represents
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SourceFoundations.monotone_represents"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SourceFoundations.monotone_represents | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SourceFoundationsStatements do
    throwError "Defining module mismatch: Thesis.SourceFoundations.monotone_represents"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SourceFoundations.monotone_represents: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SourceFoundations.monotone_represents"
#check @Thesis.SourceFoundations.monotone_represents
#print axioms _ThesisExactChecks.target_5

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_6 : Prop := (∀ {n m k : ℕ} (net : Network n m) (σ : ℝ → ℝ)
    (hw : Foundations.InputConvexWeights net) (hm : Monotone σ) (hc : Foundations.ScalarConvex σ)
    (W : Matrix (Fin k) (Fin m) ℝ) (b : Fin k → ℝ) (hW : ∀ i j, 0 ≤ W i j),
    ∀ i, ConvexOn ℝ Set.univ (fun x => (W.mulVec (net.forwardWith σ x)+b) i))
theorem _ThesisExactChecks.target_6 : _ThesisExpectedTypes.type_6 := by exact @Thesis.SourceFoundations.icnn_represents_convex
end
run_cmd do
  let target ← getConstInfo `Thesis.SourceFoundations.icnn_represents_convex
  let expected ← getConstInfo `_ThesisExactChecks.target_6
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SourceFoundations.icnn_represents_convex"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SourceFoundations.icnn_represents_convex | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SourceFoundationsStatements do
    throwError "Defining module mismatch: Thesis.SourceFoundations.icnn_represents_convex"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_6) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SourceFoundations.icnn_represents_convex: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SourceFoundations.icnn_represents_convex"
#check @Thesis.SourceFoundations.icnn_represents_convex
#print axioms _ThesisExactChecks.target_6

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_7 : Prop := (∀ {I A : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Fintype A] [Nonempty A] (w : I → ℝ) (b : ℝ) (p : Tropical.Polynomial I),
    (∀ x, relu (w ⬝ᵥ x+b) =
      ((Tropical.Polynomial.monomial w b).max (Tropical.Polynomial.monomial 0 0)).eval x) ∧
    (∀ x, (poolingPolynomial (I := I)).eval x = finiteMax x) ∧
    ConvexOn ℝ Set.univ p.eval ∧ Monotone (finiteMax (A := A)))
theorem _ThesisExactChecks.target_7 : _ThesisExpectedTypes.type_7 := by exact @Thesis.SourceFoundations.maxout_special_cases
end
run_cmd do
  let target ← getConstInfo `Thesis.SourceFoundations.maxout_special_cases
  let expected ← getConstInfo `_ThesisExactChecks.target_7
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SourceFoundations.maxout_special_cases"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SourceFoundations.maxout_special_cases | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SourceFoundationsStatements do
    throwError "Defining module mismatch: Thesis.SourceFoundations.maxout_special_cases"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_7) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SourceFoundations.maxout_special_cases: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SourceFoundations.maxout_special_cases"
#check @Thesis.SourceFoundations.maxout_special_cases
#print axioms _ThesisExactChecks.target_7

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_8 : Prop := (∀ {S A : Type} [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]
    (M : Bellman.MDP S A) (π : Bellman.Policy S A),
    ((∑' n, (M.discount : ℝ)^n • (M.markovOperator π)^[n] (M.policyReward π)) = M.policyValue π) ∧
    (M.policyBellman π (M.policyValue π) = M.policyValue π) ∧
    (∀ v, M.policyBellman π v=v → v=M.policyValue π) ∧
    (M.bellman M.optimalValue=M.optimalValue) ∧
    (∀ v, M.bellman v=v → v=M.optimalValue) ∧
    (M.policyValue (Bellman.pure M.greedy)=M.optimalValue) ∧
    (∀ ρ : Bellman.Policy S A, M.policyValue ρ ≤ M.optimalValue) ∧
    (∀ choice : S → A, (∀ s, M.action M.optimalValue s (choice s)=M.optimalValue s) →
      M.policyValue (Bellman.pure choice)=M.optimalValue))
theorem _ThesisExactChecks.target_8 : _ThesisExpectedTypes.type_8 := by exact @Thesis.SourceFoundations.bellman_equations
end
run_cmd do
  let target ← getConstInfo `Thesis.SourceFoundations.bellman_equations
  let expected ← getConstInfo `_ThesisExactChecks.target_8
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SourceFoundations.bellman_equations"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SourceFoundations.bellman_equations | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SourceFoundationsStatements do
    throwError "Defining module mismatch: Thesis.SourceFoundations.bellman_equations"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_8) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SourceFoundations.bellman_equations: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SourceFoundations.bellman_equations"
#check @Thesis.SourceFoundations.bellman_equations
#print axioms _ThesisExactChecks.target_8

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_9 : Prop := (∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A]
    (G : LayeredGames.Game S A),
    (∀ v : ℕ → S → ℝ, v 0=G.terminal →
      (∀ n s, v (n+1) s=LayeredGames.best (G.maximize n s) (fun a => G.action n s a (v n))) →
      v=G.value) ∧
    ∀ plus minus : LayeredGames.Policy S A, ∀ n s,
      G.payoff plus G.optimalPolicy n s ≤ G.value n s ∧
      G.payoff G.optimalPolicy G.optimalPolicy n s=G.value n s ∧
      G.value n s ≤ G.payoff G.optimalPolicy minus n s)
theorem _ThesisExactChecks.target_9 : _ThesisExpectedTypes.type_9 := by exact @Thesis.SourceFoundations.shapley_bellman
end
run_cmd do
  let target ← getConstInfo `Thesis.SourceFoundations.shapley_bellman
  let expected ← getConstInfo `_ThesisExactChecks.target_9
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SourceFoundations.shapley_bellman"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SourceFoundations.shapley_bellman | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SourceFoundationsStatements do
    throwError "Defining module mismatch: Thesis.SourceFoundations.shapley_bellman"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_9) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SourceFoundations.shapley_bellman: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SourceFoundations.shapley_bellman"
#check @Thesis.SourceFoundations.shapley_bellman
#print axioms _ThesisExactChecks.target_9

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_10 : Prop := (∀ {I A : Type} [Fintype I] [Fintype A] [Nonempty A]
    (v : A → I → ℝ) (x : I → ℝ),
    (∀ s, Subgradient (support (convexHull ℝ (Set.range v))) x s ↔
      s ∈ convexHull ℝ (Set.range v) ∧ s ⬝ᵥ x=support (convexHull ℝ (Set.range v)) x) ∧
    (DifferentiableAt ℝ (support (convexHull ℝ (Set.range v))) x ↔
      ∃ p, p ∈ convexHull ℝ (Set.range v) ∧
        p ⬝ᵥ x=support (convexHull ℝ (Set.range v)) x ∧
        ∀ q ∈ convexHull ℝ (Set.range v), q ⬝ᵥ x=support (convexHull ℝ (Set.range v)) x → q=p) ∧
    (∀ p, HasFDerivAt (support (convexHull ℝ (Set.range v))) (gradientRow p) x →
      p ∈ convexHull ℝ (Set.range v)))
theorem _ThesisExactChecks.target_10 : _ThesisExpectedTypes.type_10 := by exact @Thesis.SourceFoundations.subdifferential_face
end
run_cmd do
  let target ← getConstInfo `Thesis.SourceFoundations.subdifferential_face
  let expected ← getConstInfo `_ThesisExactChecks.target_10
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SourceFoundations.subdifferential_face"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SourceFoundations.subdifferential_face | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SourceFoundationsStatements do
    throwError "Defining module mismatch: Thesis.SourceFoundations.subdifferential_face"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_10) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SourceFoundations.subdifferential_face: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SourceFoundations.subdifferential_face"
#check @Thesis.SourceFoundations.subdifferential_face
#print axioms _ThesisExactChecks.target_10

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_11 : Prop := (∀ {n m k : ℕ} (net : Network n m)
    (hn : net.Nonnegative) (hb : BiasFree net)
    (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j),
    let hidden := tropicalSplit net (inputPolynomials n).1 (inputPolynomials n).2
    let g := polynomialAffine wp wn 0 hidden.1 hidden.2
    let h := polynomialAffine wn wp 0 hidden.1 hidden.2
    (∀ i, (g i).ZeroIntercepts ∧ (h i).ZeroIntercepts ∧
      (g i).NonnegativeSlopes ∧ (h i).NonnegativeSlopes ∧
      Monotone (g i).eval ∧ Monotone (h i).eval ∧
      ConvexOn ℝ Set.univ (g i).eval ∧ ConvexOn ℝ Set.univ (h i).eval ∧
      (∀ c : ℝ, 0 ≤ c → ∀ x, (g i).eval (c • x)=c*(g i).eval x ∧
        (h i).eval (c • x)=c*(h i).eval x)) ∧
    (∀ p q, (fun i => (g i).eval (Sum.elim p q))=
        wp.mulVec (net.split p q).1+wn.mulVec (net.split p q).2 ∧
      (fun i => (h i).eval (Sum.elim p q))=
        wn.mulVec (net.split p q).1+wp.mulVec (net.split p q).2) ∧
    (∀ p q i, (g i).eval (Sum.elim p q)-(h i).eval (Sum.elim p q)=
      (wp-wn).mulVec (net.eval (p-q)) i) ∧
    (∀ i, (g i).newton=(∑ j, wp i j • (hidden.1 j).newton)+
        (∑ j, wn i j • (hidden.2 j).newton) ∧
      (h i).newton=(∑ j, wn i j • (hidden.1 j).newton)+
        (∑ j, wp i j • (hidden.2 j).newton)))
theorem _ThesisExactChecks.target_11 : _ThesisExpectedTypes.type_11 := by exact @Thesis.SourceFoundations.split_tropical_rational_affine
end
run_cmd do
  let target ← getConstInfo `Thesis.SourceFoundations.split_tropical_rational_affine
  let expected ← getConstInfo `_ThesisExactChecks.target_11
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SourceFoundations.split_tropical_rational_affine"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SourceFoundations.split_tropical_rational_affine | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SourceFoundationsStatements do
    throwError "Defining module mismatch: Thesis.SourceFoundations.split_tropical_rational_affine"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_11) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SourceFoundations.split_tropical_rational_affine: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SourceFoundations.split_tropical_rational_affine"
#check @Thesis.SourceFoundations.split_tropical_rational_affine
#print axioms _ThesisExactChecks.target_11

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_12 : Prop := (∀ {I : Type} [Fintype I] (p : Thesis.Tropical.Polynomial I) (s : I → ℝ),
    (∃ x, HasFDerivAt p.eval (gradientRow s) x) ↔
      ∃ q, SliceVisible p.lift.slope q ∧ q ∈ p.lift.newton.extremePoints ℝ ∧
        inputProjection q=s)
theorem _ThesisExactChecks.target_12 : _ThesisExpectedTypes.type_12 := by exact @Thesis.SourceFoundations.biased_vertices_gradients
end
run_cmd do
  let target ← getConstInfo `Thesis.SourceFoundations.biased_vertices_gradients
  let expected ← getConstInfo `_ThesisExactChecks.target_12
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SourceFoundations.biased_vertices_gradients"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SourceFoundations.biased_vertices_gradients | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SourceFoundationsStatements do
    throwError "Defining module mismatch: Thesis.SourceFoundations.biased_vertices_gradients"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_12) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SourceFoundations.biased_vertices_gradients: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SourceFoundations.biased_vertices_gradients"
#check @Thesis.SourceFoundations.biased_vertices_gradients
#print axioms _ThesisExactChecks.target_12

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_13 : Prop := (∀ {n m k : ℕ} (net : Network n m) (hn : net.Nonnegative)
    (hr : ReLUNetGame.NonzeroRows net) (x : Fin n → ℝ)
    (plus minus : ReLUNetGame.Strategy net) (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (b : Fin k → ℝ) (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j)
    (hrow : ∀ i, ReLUNetGame.rowDiscount wp wn i≠0) (i : Fin k),
    let read := fun v : (Fin m → ℝ) × (Fin m → ℝ) => ReLUNetGame.continuation wp wn b v.1 v.2 i
    let logit := ((wp-wn).mulVec (net.eval x)+b) i
    read (ReLUNetGame.policyValue net plus (ReLUNetGame.optimalStrategy net x) x (-x)) ≤ logit ∧
    read (ReLUNetGame.policyValue net (ReLUNetGame.optimalStrategy net x)
      (ReLUNetGame.optimalStrategy net x) x (-x))=logit ∧
    logit ≤ read (ReLUNetGame.policyValue net (ReLUNetGame.optimalStrategy net x) minus x (-x)) ∧
    (ReLUNetGame.SubgamePerfect net plus minus x (-x) ↔
      ReLUNetGame.GateOptimalStrategy net x plus ∧ ReLUNetGame.GateOptimalStrategy net x minus) ∧
    (ReLUNetGame.SubgamePerfect net plus minus x (-x) →
      read (ReLUNetGame.policyValue net plus minus x (-x))=logit))
theorem _ThesisExactChecks.target_13 : _ThesisExpectedTypes.type_13 := by exact @Thesis.SourceFoundations.relu_net_game_value_affine
end
run_cmd do
  let target ← getConstInfo `Thesis.SourceFoundations.relu_net_game_value_affine
  let expected ← getConstInfo `_ThesisExactChecks.target_13
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SourceFoundations.relu_net_game_value_affine"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SourceFoundations.relu_net_game_value_affine | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SourceFoundationsStatements do
    throwError "Defining module mismatch: Thesis.SourceFoundations.relu_net_game_value_affine"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_13) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SourceFoundations.relu_net_game_value_affine: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SourceFoundations.relu_net_game_value_affine"
#check @Thesis.SourceFoundations.relu_net_game_value_affine
#print axioms _ThesisExactChecks.target_13

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_14 : Prop := (∀ {I A : Type} [Fintype I] [Fintype A] [Nonempty A] (P Q : Set (I → ℝ)) (hP : IsCompact P) (hneP : P.Nonempty)
    (hcP : Convex ℝ P) (hQ : IsCompact Q) (hneQ : Q.Nonempty) (hcQ : Convex ℝ Q),
    ConvexOn ℝ Set.univ (support P) ∧
    (∀ c : ℝ, 0 ≤ c → ∀ x, support P (c • x) = c*support P x) ∧
    (∀ x, support (P+Q) x = support P x+support Q x) ∧
    (∀ x, support (convexHull ℝ (P∪Q)) x = max (support P x) (support Q x)) ∧
    (P ⊆ Q ↔ ∀ x, support P x ≤ support Q x) ∧
    (support P = support Q → P = Q) ∧
    (∀ (v : A → I → ℝ) x, support (convexHull ℝ (Set.range v)) x = finiteMax (fun a => v a ⬝ᵥ x) ∧
      ∃ p ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ,
        p ⬝ᵥ x = support (convexHull ℝ (Set.range v)) x))
theorem _ThesisExactChecks.target_14 : _ThesisExpectedTypes.type_14 := by exact @Thesis.SourceGeometry.support_properties
end
run_cmd do
  let target ← getConstInfo `Thesis.SourceGeometry.support_properties
  let expected ← getConstInfo `_ThesisExactChecks.target_14
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SourceGeometry.support_properties"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SourceGeometry.support_properties | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SourceGeometryStatements do
    throwError "Defining module mismatch: Thesis.SourceGeometry.support_properties"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_14) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SourceGeometry.support_properties: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SourceGeometry.support_properties"
#check @Thesis.SourceGeometry.support_properties
#print axioms _ThesisExactChecks.target_14

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_15 : Prop := (∀ {I : Type} [Fintype I] (p q : Tropical.Polynomial I),
    (p.add q).newton = p.newton+q.newton ∧
    (p.max q).newton = convexHull ℝ (p.newton∪q.newton) ∧
    (∀ x, (p.add q).eval x=p.eval x+q.eval x) ∧
    (∀ x, (p.max q).eval x=max (p.eval x) (q.eval x)) ∧
    (∀ x, p.eval x=support p.lift.newton (Sum.elim x (fun _ => 1))) ∧
    ((∀ a, p.intercept a=0) → ∀ x, p.eval x=support p.newton x))
theorem _ThesisExactChecks.target_15 : _ThesisExpectedTypes.type_15 := by exact @Thesis.SourceGeometry.newton_calculus
end
run_cmd do
  let target ← getConstInfo `Thesis.SourceGeometry.newton_calculus
  let expected ← getConstInfo `_ThesisExactChecks.target_15
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SourceGeometry.newton_calculus"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SourceGeometry.newton_calculus | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SourceGeometryStatements do
    throwError "Defining module mismatch: Thesis.SourceGeometry.newton_calculus"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_15) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SourceGeometry.newton_calculus: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SourceGeometry.newton_calculus"
#check @Thesis.SourceGeometry.newton_calculus
#print axioms _ThesisExactChecks.target_15

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_16 : Prop := (∀ {n m : ℕ} (net : Network n m) (hn : net.Nonnegative)
    (i : Fin m),
    let polynomials := tropicalSplit net (inputPolynomials n).1 (inputPolynomials n).2
    (∀ v ∈ (polynomials.1 i).newton, ∀ j, 0 ≤ v j) ∧
    (∀ v ∈ (polynomials.2 i).newton, ∀ j, 0 ≤ v j))
theorem _ThesisExactChecks.target_16 : _ThesisExpectedTypes.type_16 := by exact @Thesis.SourceGeometry.network_polytopes_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.SourceGeometry.network_polytopes_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_16
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SourceGeometry.network_polytopes_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SourceGeometry.network_polytopes_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SourceGeometryStatements do
    throwError "Defining module mismatch: Thesis.SourceGeometry.network_polytopes_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_16) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SourceGeometry.network_polytopes_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SourceGeometry.network_polytopes_nonnegative"
#check @Thesis.SourceGeometry.network_polytopes_nonnegative
#print axioms _ThesisExactChecks.target_16

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_17 : Prop := (∀ {n m k : ℕ} (net : Network n m)
    (wp wn : Matrix (Fin k) (Fin m) ℝ) (bp bn : Fin k → ℝ),
    let hidden := tropicalSplit net (inputPolynomials n).1 (inputPolynomials n).2
    let sets := polytopeSplit net (fun j => {Pi.single (Sum.inl j : Fin n ⊕ Fin n) (1 : ℝ)})
      (fun j => {Pi.single (Sum.inr j : Fin n ⊕ Fin n) (1 : ℝ)})
    (∀ i, (hidden.1 i).newton=sets.1 i ∧ (hidden.2 i).newton=sets.2 i) ∧
    ∀ i, (polynomialAffine wp wn bp hidden.1 hidden.2 i).newton=
        (∑ j, wp i j • sets.1 j)+(∑ j, wn i j • sets.2 j) ∧
      (polynomialAffine wn wp bn hidden.1 hidden.2 i).newton=
        (∑ j, wn i j • sets.1 j)+(∑ j, wp i j • sets.2 j))
theorem _ThesisExactChecks.target_17 : _ThesisExpectedTypes.type_17 := by exact @Thesis.SourceGeometry.minkowski_propagation_affine_network
end
run_cmd do
  let target ← getConstInfo `Thesis.SourceGeometry.minkowski_propagation_affine_network
  let expected ← getConstInfo `_ThesisExactChecks.target_17
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SourceGeometry.minkowski_propagation_affine_network"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SourceGeometry.minkowski_propagation_affine_network | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SourceGeometryStatements do
    throwError "Defining module mismatch: Thesis.SourceGeometry.minkowski_propagation_affine_network"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_17) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SourceGeometry.minkowski_propagation_affine_network: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SourceGeometry.minkowski_propagation_affine_network"
#check @Thesis.SourceGeometry.minkowski_propagation_affine_network
#print axioms _ThesisExactChecks.target_17

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_18 : Prop := (∀ {n m : ℕ} (net : Network n m),
    CPWL net.eval)
theorem _ThesisExactChecks.target_18 : _ThesisExpectedTypes.type_18 := by exact @Thesis.PiecewiseLinear.network_cpwl
end
run_cmd do
  let target ← getConstInfo `Thesis.PiecewiseLinear.network_cpwl
  let expected ← getConstInfo `_ThesisExactChecks.target_18
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.PiecewiseLinear.network_cpwl"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.PiecewiseLinear.network_cpwl | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.PiecewiseLinear do
    throwError "Defining module mismatch: Thesis.PiecewiseLinear.network_cpwl"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_18) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.PiecewiseLinear.network_cpwl: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.PiecewiseLinear.network_cpwl"
#check @Thesis.PiecewiseLinear.network_cpwl
#print axioms _ThesisExactChecks.target_18

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_19 : Prop := (∀ {n m k : ℕ} (net : Network n m)
    (W : Matrix (Fin k) (Fin m) ℝ) (b : Fin k → ℝ),
    CPWL (fun x => W.mulVec (net.eval x)+b))
theorem _ThesisExactChecks.target_19 : _ThesisExpectedTypes.type_19 := by exact @Thesis.PiecewiseLinear.affine_network_cpwl
end
run_cmd do
  let target ← getConstInfo `Thesis.PiecewiseLinear.affine_network_cpwl
  let expected ← getConstInfo `_ThesisExactChecks.target_19
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.PiecewiseLinear.affine_network_cpwl"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.PiecewiseLinear.affine_network_cpwl | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.PiecewiseLinear do
    throwError "Defining module mismatch: Thesis.PiecewiseLinear.affine_network_cpwl"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_19) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.PiecewiseLinear.affine_network_cpwl: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.PiecewiseLinear.affine_network_cpwl"
#check @Thesis.PiecewiseLinear.affine_network_cpwl
#print axioms _ThesisExactChecks.target_19

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_20 : Prop := (∀ {I : Type} [Fintype I] (u : (I → ℝ) → ℝ),
    (CPWL (fun x (_ : Unit) => u x) ∧ ConvexOn ℝ Set.univ u) ↔
      ∃ p : Polynomial I, u=p.eval)
theorem _ThesisExactChecks.target_20 : _ThesisExpectedTypes.type_20 := by exact @Thesis.PiecewiseLinear.convex_cpwl_iff_max_affine
end
run_cmd do
  let target ← getConstInfo `Thesis.PiecewiseLinear.convex_cpwl_iff_max_affine
  let expected ← getConstInfo `_ThesisExactChecks.target_20
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.PiecewiseLinear.convex_cpwl_iff_max_affine"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.PiecewiseLinear.convex_cpwl_iff_max_affine | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConvexCPWL do
    throwError "Defining module mismatch: Thesis.PiecewiseLinear.convex_cpwl_iff_max_affine"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_20) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.PiecewiseLinear.convex_cpwl_iff_max_affine: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.PiecewiseLinear.convex_cpwl_iff_max_affine"
#check @Thesis.PiecewiseLinear.convex_cpwl_iff_max_affine
#print axioms _ThesisExactChecks.target_20

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_21 : Prop := (∀ {I : Type} [Fintype I] (u : (I → ℝ) → ℝ)
    (hp : CPWL (fun x (_ : Unit) => u x)) (hc : ConvexOn ℝ Set.univ u)
    (hh : ∀ c : ℝ, 0 ≤ c → ∀ x, u (c • x)=c*u x),
    ∃! P : Set (I → ℝ), IsPolytope P ∧ u=support P)
theorem _ThesisExactChecks.target_21 : _ThesisExpectedTypes.type_21 := by exact @Thesis.PiecewiseLinear.homogeneous_convex_cpwl_unique_polytope
end
run_cmd do
  let target ← getConstInfo `Thesis.PiecewiseLinear.homogeneous_convex_cpwl_unique_polytope
  let expected ← getConstInfo `_ThesisExactChecks.target_21
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.PiecewiseLinear.homogeneous_convex_cpwl_unique_polytope"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.PiecewiseLinear.homogeneous_convex_cpwl_unique_polytope | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConvexCPWL do
    throwError "Defining module mismatch: Thesis.PiecewiseLinear.homogeneous_convex_cpwl_unique_polytope"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_21) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.PiecewiseLinear.homogeneous_convex_cpwl_unique_polytope: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.PiecewiseLinear.homogeneous_convex_cpwl_unique_polytope"
#check @Thesis.PiecewiseLinear.homogeneous_convex_cpwl_unique_polytope
#print axioms _ThesisExactChecks.target_21

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_22 : Prop := (∀ {I : Type} [Fintype I] (u : (I → ℝ) → ℝ)
    (hp : CPWL (fun x (_ : Unit) => u x)) (hc : ConvexOn ℝ Set.univ u)
    (hh : ∀ c : ℝ, 0 ≤ c → ∀ x, u (c • x)=c*u x),
    ∃ P : Set (I → ℝ), IsPolytope P ∧ u=support P ∧
      (∀ Q, IsPolytope Q → u=support Q → Q=P) ∧
      ∀ s, s ∈ P.extremePoints ℝ ↔ ∃ x, HasFDerivAt u (gradientRow s) x)
theorem _ThesisExactChecks.target_22 : _ThesisExpectedTypes.type_22 := by exact @Thesis.PiecewiseLinear.homogeneous_convex_cpwl_vertices
end
run_cmd do
  let target ← getConstInfo `Thesis.PiecewiseLinear.homogeneous_convex_cpwl_vertices
  let expected ← getConstInfo `_ThesisExactChecks.target_22
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.PiecewiseLinear.homogeneous_convex_cpwl_vertices"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.PiecewiseLinear.homogeneous_convex_cpwl_vertices | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConvexCPWL do
    throwError "Defining module mismatch: Thesis.PiecewiseLinear.homogeneous_convex_cpwl_vertices"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_22) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.PiecewiseLinear.homogeneous_convex_cpwl_vertices: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.PiecewiseLinear.homogeneous_convex_cpwl_vertices"
#check @Thesis.PiecewiseLinear.homogeneous_convex_cpwl_vertices
#print axioms _ThesisExactChecks.target_22

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_23 : Prop := (∀ {n m : ℕ} (net : Network n m)
    (hr : NonzeroRows net) (x : Fin n → ℝ) (plus minus : Strategy net),
    SubgamePerfect net plus minus x (-x) ↔
      GateOptimalStrategy net x plus ∧ GateOptimalStrategy net x minus)
theorem _ThesisExactChecks.target_23 : _ThesisExpectedTypes.type_23 := by exact @Thesis.ReLUNetGame.subgamePerfect_iff_gateOptimal
end
run_cmd do
  let target ← getConstInfo `Thesis.ReLUNetGame.subgamePerfect_iff_gateOptimal
  let expected ← getConstInfo `_ThesisExactChecks.target_23
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ReLUNetGame.subgamePerfect_iff_gateOptimal"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReLUNetGame.subgamePerfect_iff_gateOptimal | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReLUNetEquilibrium do
    throwError "Defining module mismatch: Thesis.ReLUNetGame.subgamePerfect_iff_gateOptimal"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_23) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ReLUNetGame.subgamePerfect_iff_gateOptimal: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReLUNetGame.subgamePerfect_iff_gateOptimal"
#check @Thesis.ReLUNetGame.subgamePerfect_iff_gateOptimal
#print axioms _ThesisExactChecks.target_23

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_24 : Prop := (∀ {n m : ℕ} (net : Network n m)
    (hr : NonzeroRows net) (x : Fin n → ℝ),
    SubgamePerfect net (optimalStrategy net x) (optimalStrategy net x) x (-x))
theorem _ThesisExactChecks.target_24 : _ThesisExpectedTypes.type_24 := by exact @Thesis.ReLUNetGame.optimalStrategy_subgamePerfect
end
run_cmd do
  let target ← getConstInfo `Thesis.ReLUNetGame.optimalStrategy_subgamePerfect
  let expected ← getConstInfo `_ThesisExactChecks.target_24
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ReLUNetGame.optimalStrategy_subgamePerfect"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReLUNetGame.optimalStrategy_subgamePerfect | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReLUNetEquilibrium do
    throwError "Defining module mismatch: Thesis.ReLUNetGame.optimalStrategy_subgamePerfect"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_24) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ReLUNetGame.optimalStrategy_subgamePerfect: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReLUNetGame.optimalStrategy_subgamePerfect"
#check @Thesis.ReLUNetGame.optimalStrategy_subgamePerfect
#print axioms _ThesisExactChecks.target_24

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_25 : Prop := (∀ {n m : ℕ} (net : Network n m) (hr : NonzeroRows net)
    (x : Fin n → ℝ) (plus minus : Strategy net)
    (h : SubgamePerfect net plus minus x (-x)),
    policyValue net plus minus x (-x)=(net.eval x,-net.eval x))
theorem _ThesisExactChecks.target_25 : _ThesisExpectedTypes.type_25 := by exact @Thesis.ReLUNetGame.subgamePerfect_value
end
run_cmd do
  let target ← getConstInfo `Thesis.ReLUNetGame.subgamePerfect_value
  let expected ← getConstInfo `_ThesisExactChecks.target_25
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ReLUNetGame.subgamePerfect_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReLUNetGame.subgamePerfect_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReLUNetEquilibrium do
    throwError "Defining module mismatch: Thesis.ReLUNetGame.subgamePerfect_value"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_25) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ReLUNetGame.subgamePerfect_value: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReLUNetGame.subgamePerfect_value"
#check @Thesis.ReLUNetGame.subgamePerfect_value
#print axioms _ThesisExactChecks.target_25

section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal
def _ThesisExpectedTypes.type_26 : Prop := (∀ {I A : Type} [Fintype I] [Fintype A] [Nonempty A] (v : A → I ⊕ Unit → ℝ) (s : I → ℝ),
    (∃ x, HasFDerivAt (fun y => support (convexHull ℝ (Set.range v)) (affineSlice y))
      (gradientRow s) x) ↔
    ∃ p, SliceVisible v p ∧ p ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ ∧
      inputProjection p=s)
theorem _ThesisExactChecks.target_26 : _ThesisExpectedTypes.type_26 := by exact @Thesis.Tropical.slice_attainable_gradients
end
run_cmd do
  let target ← getConstInfo `Thesis.Tropical.slice_attainable_gradients
  let expected ← getConstInfo `_ThesisExactChecks.target_26
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Tropical.slice_attainable_gradients"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Tropical.slice_attainable_gradients | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AffineSliceGeometry do
    throwError "Defining module mismatch: Thesis.Tropical.slice_attainable_gradients"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_26) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Tropical.slice_attainable_gradients: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Tropical.slice_attainable_gradients"
#check @Thesis.Tropical.slice_attainable_gradients
#print axioms _ThesisExactChecks.target_26

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_27 : Prop := (∀ {n m : ℕ} (net : Network n m) (rp rn : Row m) (bp bn : ℝ) (x : PairVec n),
 (net.affineHeads rp rn bp bn x).1 - (net.affineHeads rp rn bp bn x).2 = net.affineLogit rp rn bp bn (x.1-x.2))
theorem _ThesisExactChecks.target_27 : _ThesisExpectedTypes.type_27 := by exact @HiddenMonotonicity.Network.affine_heads_recovery
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_heads_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_27
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_heads_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_heads_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.AffineHeads do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_heads_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_27) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_heads_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_heads_recovery"
#check @HiddenMonotonicity.Network.affine_heads_recovery
#print axioms _ThesisExactChecks.target_27

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_28 : Prop := (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (x : Vec n) (hx : net.Strict x) (rp rn : Row m) (bp bn : ℝ),
 HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1)
 ((1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac - (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x ∧
 HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2)
 ((-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac + (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x)
theorem _ThesisExactChecks.target_28 : _ThesisExpectedTypes.type_28 := by exact @HiddenMonotonicity.Network.affine_plain_head_formulas
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_plain_head_formulas
  let expected ← getConstInfo `_ThesisExactChecks.target_28
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_plain_head_formulas"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_plain_head_formulas | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.AffineHeads do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_plain_head_formulas"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_28) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_plain_head_formulas: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_plain_head_formulas"
#check @HiddenMonotonicity.Network.affine_plain_head_formulas
#print axioms _ThesisExactChecks.target_28

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_29 : Prop := (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (x : Vec n) (w : Vec m) (head : Bool),
 ((net.originalTrace x).run (fun _ => 0) (affineReadoutSeed (coefficientRow (fun i => max (w i) 0)) (coefficientRow (fun i => max (-w i) 0)) 0 head)).1 +
 ((net.originalTrace x).run (fun _ => 0) (affineReadoutSeed (coefficientRow (fun i => max (w i) 0)) (coefficientRow (fun i => max (-w i) 0)) 0 head)).2 =
 (coefficientRow (fun i => |w i|)).comp net.absoluteMap)
theorem _ThesisExactChecks.target_29 : _ThesisExpectedTypes.type_29 := by exact @HiddenMonotonicity.Network.affine_canonical_mass
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_canonical_mass
  let expected ← getConstInfo `_ThesisExactChecks.target_29
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_canonical_mass"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_canonical_mass | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.AffineHeads do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_canonical_mass"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_29) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_canonical_mass: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_canonical_mass"
#check @HiddenMonotonicity.Network.affine_canonical_mass
#print axioms _ThesisExactChecks.target_29

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_30 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
 (hw : ∀ i j, 0≤wp i j ∧ 0≤wn i j) (hb : 0≤bp ∧ 0≤bn),
 (∀ x, (affineChunk wp wn bp bn x).1-(affineChunk wp wn bp bn x).2 = affineLayer wp wn bp bn (x.1-x.2)) ∧
 (∀ x, 0≤x → 0≤affineChunk wp wn bp bn x) ∧ Monotone (affineChunk wp wn bp bn) ∧
 (∀ x y (a b : ℝ), a+b=1 → affineChunk wp wn bp bn (a • x+b • y) = a • affineChunk wp wn bp bn x+b • affineChunk wp wn bp bn y) ∧
 (∀ i, ConvexOn ℝ Set.univ (fun x => (affineChunk wp wn bp bn x).1 i) ∧ ConvexOn ℝ Set.univ (fun x => (affineChunk wp wn bp bn x).2 i)))
theorem _ThesisExactChecks.target_30 : _ThesisExpectedTypes.type_30 := by exact @HiddenMonotonicity.linear_chunk_properties
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.linear_chunk_properties
  let expected ← getConstInfo `_ThesisExactChecks.target_30
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.linear_chunk_properties"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.linear_chunk_properties | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.AffineChunk do
    throwError "Defining module mismatch: HiddenMonotonicity.linear_chunk_properties"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_30) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.linear_chunk_properties: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.linear_chunk_properties"
#check @HiddenMonotonicity.linear_chunk_properties
#print axioms _ThesisExactChecks.target_30

section
universe u
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_31 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] [DecidableEq ι],
 (∀ x, (finitePool (ι := ι) x).1-(finitePool x).2 = Finset.univ.sup' Finset.univ_nonempty (fun j => x.1 j-x.2 j)) ∧
 (∀ x, 0≤x → 0≤finitePool (ι := ι) x) ∧ Monotone (finitePool (ι := ι)) ∧
 ConvexOn ℝ Set.univ (fun x => (finitePool (ι := ι) x).1) ∧ ConvexOn ℝ Set.univ (fun x => (finitePool (ι := ι) x).2))
theorem _ThesisExactChecks.target_31 : _ThesisExpectedTypes.type_31.{u} := by exact @HiddenMonotonicity.maxpool_properties.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.maxpool_properties
  let expected ← getConstInfo `_ThesisExactChecks.target_31
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.maxpool_properties"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.maxpool_properties | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MaxPool do
    throwError "Defining module mismatch: HiddenMonotonicity.maxpool_properties"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_31) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.maxpool_properties: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.maxpool_properties"
#check @HiddenMonotonicity.maxpool_properties
#print axioms _ThesisExactChecks.target_31

section
universe u
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_32 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (x : (ι → ℝ) × (ι → ℝ)),
 (winnerPool x).1-(winnerPool x).2 = Finset.univ.sup' Finset.univ_nonempty (fun j => x.1 j-x.2 j))
theorem _ThesisExactChecks.target_32 : _ThesisExpectedTypes.type_32.{u} := by exact @HiddenMonotonicity.winnerPool_recovery.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.winnerPool_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_32
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.winnerPool_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.winnerPool_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MaxPool do
    throwError "Defining module mismatch: HiddenMonotonicity.winnerPool_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_32) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.winnerPool_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.winnerPool_recovery"
#check @HiddenMonotonicity.winnerPool_recovery
#print axioms _ThesisExactChecks.target_32

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_33 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (pooling : ℕ → PoolingRule) (center : ℕ → Bool) (x : Fin d × Bool → ℝ),
 (c.splitWithPolicy pooling center x).1-(c.splitWithPolicy pooling center x).2 = c.eval (fun i => x (i,false)-x (i,true)))
theorem _ThesisExactChecks.target_33 : _ThesisExpectedTypes.type_33 := by exact @HiddenMonotonicity.Circuit.split_policy_correct
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Circuit.split_policy_correct
  let expected ← getConstInfo `_ThesisExactChecks.target_33
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Circuit.split_policy_correct"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Circuit.split_policy_correct | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PoolingCircuit do
    throwError "Defining module mismatch: HiddenMonotonicity.Circuit.split_policy_correct"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_33) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Circuit.split_policy_correct: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Circuit.split_policy_correct"
#check @HiddenMonotonicity.Circuit.split_policy_correct
#print axioms _ThesisExactChecks.target_33

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_34 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (pooling : ℕ → PoolingRule) (center : ℕ → Bool) (x : Fin d × Bool → ℝ) (hx : 0≤x),
 0≤c.splitWithPolicy pooling center x)
theorem _ThesisExactChecks.target_34 : _ThesisExpectedTypes.type_34 := by exact @HiddenMonotonicity.Circuit.split_policy_nonnegative
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Circuit.split_policy_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_34
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Circuit.split_policy_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Circuit.split_policy_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PoolingCircuit do
    throwError "Defining module mismatch: HiddenMonotonicity.Circuit.split_policy_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_34) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Circuit.split_policy_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Circuit.split_policy_nonnegative"
#check @HiddenMonotonicity.Circuit.split_policy_nonnegative
#print axioms _ThesisExactChecks.target_34

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_35 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (center : Bool) (x : Fin d × Bool → ℝ),
 c.splitWithPolicy (fun _ => PoolingRule.convex) (fun _ => center) x = c.split center x)
theorem _ThesisExactChecks.target_35 : _ThesisExpectedTypes.type_35 := by exact @HiddenMonotonicity.Circuit.split_policy_convex_eq
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Circuit.split_policy_convex_eq
  let expected ← getConstInfo `_ThesisExactChecks.target_35
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Circuit.split_policy_convex_eq"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Circuit.split_policy_convex_eq | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PoolingCircuit do
    throwError "Defining module mismatch: HiddenMonotonicity.Circuit.split_policy_convex_eq"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_35) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Circuit.split_policy_convex_eq: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Circuit.split_policy_convex_eq"
#check @HiddenMonotonicity.Circuit.split_policy_convex_eq
#print axioms _ThesisExactChecks.target_35

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_36 : Prop := (∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative) (x : PairVec n) (rp rn : Row m)
 (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ) (head : Bool)
 (hd : DifferentiableAt ℝ (fun y => if head then (net.affineHeads rp rn bp bn y).1 else (net.affineHeads rp rn bp bn y).2) x),
 HasFDerivAt (fun y => if head then (net.affineHeads rp rn bp bn y).1 else (net.affineHeads rp rn bp bn y).2)
 (assemble ((net.originalTrace (x.1-x.2)).run (fun _ => 0) (affineReadoutSeed rp rn 0 head))) x)
theorem _ThesisExactChecks.target_36 : _ThesisExpectedTypes.type_36 := by exact @HiddenMonotonicity.Network.affine_head_derivative_of_differentiable
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_head_derivative_of_differentiable
  let expected ← getConstInfo `_ThesisExactChecks.target_36
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_head_derivative_of_differentiable"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_head_derivative_of_differentiable | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.DifferentiableHeads do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_head_derivative_of_differentiable"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_36) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_head_derivative_of_differentiable: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_head_derivative_of_differentiable"
#check @HiddenMonotonicity.Network.affine_head_derivative_of_differentiable
#print axioms _ThesisExactChecks.target_36

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_37 : Prop := (∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative) (x : Vec n) (rp rn : Row m)
 (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ) (head : Bool)
 (hd : DifferentiableAt ℝ (fun y => if head then (net.affineHeads rp rn bp bn (balancedLift n y)).1 else (net.affineHeads rp rn bp bn (balancedLift n y)).2) x),
 HasFDerivAt (fun y => if head then (net.affineHeads rp rn bp bn (balancedLift n y)).1 else (net.affineHeads rp rn bp bn (balancedLift n y)).2)
 (unified ((net.originalTrace x).run (fun _ => 0) (affineReadoutSeed rp rn 0 head))) x)
theorem _ThesisExactChecks.target_37 : _ThesisExpectedTypes.type_37 := by exact @HiddenMonotonicity.Network.affine_symmetric_derivative_of_differentiable
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_symmetric_derivative_of_differentiable
  let expected ← getConstInfo `_ThesisExactChecks.target_37
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_symmetric_derivative_of_differentiable"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_symmetric_derivative_of_differentiable | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.DifferentiableHeads do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_symmetric_derivative_of_differentiable"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_37) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_symmetric_derivative_of_differentiable: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_symmetric_derivative_of_differentiable"
#check @HiddenMonotonicity.Network.affine_symmetric_derivative_of_differentiable
#print axioms _ThesisExactChecks.target_37

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_38 : Prop := (∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative) (x : Vec n) (rp rn : Row m)
 (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ)
 (hg : DifferentiableAt ℝ (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1) x)
 (hh : DifferentiableAt ℝ (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2) x)
 (α : ℕ → ℝ) (β : ℝ),
 HasFDerivAt (net.affineLogit rp rn bp bn) ((rp-rn).comp (net.originalTrace x).originalJac) x ∧
 ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)).1-((net.originalTrace x).run α (affineReadoutSeed rp rn β false)).1 = (rp-rn).comp (net.originalTrace x).originalJac ∧
 ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)).2-((net.originalTrace x).run α (affineReadoutSeed rp rn β false)).2 = -((rp-rn).comp (net.originalTrace x).originalJac))
theorem _ThesisExactChecks.target_38 : _ThesisExpectedTypes.type_38 := by exact @HiddenMonotonicity.Network.affine_backward_invariants_of_differentiable
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_backward_invariants_of_differentiable
  let expected ← getConstInfo `_ThesisExactChecks.target_38
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_backward_invariants_of_differentiable"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_backward_invariants_of_differentiable | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.DifferentiableHeads do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_backward_invariants_of_differentiable"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_38) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_backward_invariants_of_differentiable: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_backward_invariants_of_differentiable"
#check @HiddenMonotonicity.Network.affine_backward_invariants_of_differentiable
#print axioms _ThesisExactChecks.target_38

section
open HiddenMonotonicity MeasureTheory
open scoped BigOperators
def _ThesisExpectedTypes.type_39 : Prop := (∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative) (rp rn : Row m) (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ),
 ∀ᵐ x : Vec n, ∀ head : Bool,
 HasFDerivAt (fun y => if head then (net.affineHeads rp rn bp bn (balancedLift n y)).1 else (net.affineHeads rp rn bp bn (balancedLift n y)).2)
 (unified ((net.originalTrace x).run (fun _ => 0) (affineReadoutSeed rp rn 0 head))) x)
theorem _ThesisExactChecks.target_39 : _ThesisExpectedTypes.type_39 := by exact @HiddenMonotonicity.Network.affine_heads_ae_derivatives
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_heads_ae_derivatives
  let expected ← getConstInfo `_ThesisExactChecks.target_39
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_heads_ae_derivatives"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_heads_ae_derivatives | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.AlmostEverywhere do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_heads_ae_derivatives"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_39) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_heads_ae_derivatives: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_heads_ae_derivatives"
#check @HiddenMonotonicity.Network.affine_heads_ae_derivatives
#print axioms _ThesisExactChecks.target_39

section
open HiddenMonotonicity MeasureTheory
open scoped BigOperators
def _ThesisExpectedTypes.type_40 : Prop := (∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative) (rp rn : Row m) (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ),
 ∀ᵐ x : Vec n, ∀ (α : ℕ → ℝ) (β : ℝ),
 HasFDerivAt (net.affineLogit rp rn bp bn) ((rp-rn).comp (net.originalTrace x).originalJac) x ∧
 ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)).1-((net.originalTrace x).run α (affineReadoutSeed rp rn β false)).1 = (rp-rn).comp (net.originalTrace x).originalJac ∧
 ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)).2-((net.originalTrace x).run α (affineReadoutSeed rp rn β false)).2 = -((rp-rn).comp (net.originalTrace x).originalJac))
theorem _ThesisExactChecks.target_40 : _ThesisExpectedTypes.type_40 := by exact @HiddenMonotonicity.Network.affine_ae_backward_invariants
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_ae_backward_invariants
  let expected ← getConstInfo `_ThesisExactChecks.target_40
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_ae_backward_invariants"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_ae_backward_invariants | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.AlmostEverywhere do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_ae_backward_invariants"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_40) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_ae_backward_invariants: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_ae_backward_invariants"
#check @HiddenMonotonicity.Network.affine_ae_backward_invariants
#print axioms _ThesisExactChecks.target_40

section
open HiddenMonotonicity MeasureTheory
open scoped BigOperators
def _ThesisExpectedTypes.type_41 : Prop := (∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative),
 ∀ᵐ x : Vec n, HasFDerivAt net.eval (net.originalTrace x).originalJac x)
theorem _ThesisExactChecks.target_41 : _ThesisExpectedTypes.type_41 := by exact @HiddenMonotonicity.Network.originalTrace_ae_derivative
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.originalTrace_ae_derivative
  let expected ← getConstInfo `_ThesisExactChecks.target_41
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.originalTrace_ae_derivative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.originalTrace_ae_derivative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PrefixSources do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.originalTrace_ae_derivative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_41) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.originalTrace_ae_derivative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.originalTrace_ae_derivative"
#check @HiddenMonotonicity.Network.originalTrace_ae_derivative
#print axioms _ThesisExactChecks.target_41

section
open HiddenMonotonicity MeasureTheory
open scoped BigOperators
def _ThesisExpectedTypes.type_42 : Prop := (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (α : ℕ → ℝ),
 ∀ᵐ x : Vec n, ∀ q ∈ net.absoluteQSources x α, HasFDerivAt q.value q.jacobian x)
theorem _ThesisExactChecks.target_42 : _ThesisExpectedTypes.type_42 := by exact @HiddenMonotonicity.Network.absoluteQSources_ae_derivatives
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.absoluteQSources_ae_derivatives
  let expected ← getConstInfo `_ThesisExactChecks.target_42
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.absoluteQSources_ae_derivatives"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.absoluteQSources_ae_derivatives | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PrefixSources do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.absoluteQSources_ae_derivatives"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_42) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.absoluteQSources_ae_derivatives: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.absoluteQSources_ae_derivatives"
#check @HiddenMonotonicity.Network.absoluteQSources_ae_derivatives
#print axioms _ThesisExactChecks.target_42

section
open HiddenMonotonicity MeasureTheory
open scoped BigOperators
def _ThesisExpectedTypes.type_43 : Prop := (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (x : Vec n) (α : ℕ → ℝ) (rp rn : Row m) (β : ℝ),
unified ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)) =
 (1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac - (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rp+rn))).sum) ∧
 unified ((net.originalTrace x).run α (affineReadoutSeed rp rn β false)) =
 (-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac + (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rp+rn))).sum))
theorem _ThesisExactChecks.target_43 : _ThesisExpectedTypes.type_43 := by exact @HiddenMonotonicity.Network.affine_Q_row_formulas
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_Q_row_formulas
  let expected ← getConstInfo `_ThesisExactChecks.target_43
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_Q_row_formulas"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_Q_row_formulas | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.DifferentiableBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_Q_row_formulas"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_43) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_Q_row_formulas: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_Q_row_formulas"
#check @HiddenMonotonicity.Network.affine_Q_row_formulas
#print axioms _ThesisExactChecks.target_43

section
open HiddenMonotonicity MeasureTheory
open scoped BigOperators
def _ThesisExpectedTypes.type_44 : Prop := (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (α : ℕ → ℝ) (rp rn : Row m) (bp bn β : ℝ),
 ∀ᵐ x : Vec n,
 (∀ q ∈ net.absoluteQSources x α, HasFDerivAt q.value q.jacobian x) ∧
 HasFDerivAt (net.affineLogit rp rn bp bn) ((rp-rn).comp (net.originalTrace x).originalJac) x ∧
unified ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)) =
 (1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac - (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rp+rn))).sum) ∧
 unified ((net.originalTrace x).run α (affineReadoutSeed rp rn β false)) =
 (-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac + (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rp+rn))).sum))
theorem _ThesisExactChecks.target_44 : _ThesisExpectedTypes.type_44 := by exact @HiddenMonotonicity.Network.affine_Q_closed_form_ae
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_Q_closed_form_ae
  let expected ← getConstInfo `_ThesisExactChecks.target_44
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_Q_closed_form_ae"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_Q_closed_form_ae | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.DifferentiableBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_Q_closed_form_ae"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_44) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_Q_closed_form_ae: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_Q_closed_form_ae"
#check @HiddenMonotonicity.Network.affine_Q_closed_form_ae
#print axioms _ThesisExactChecks.target_44

section
open HiddenMonotonicity MeasureTheory
open scoped BigOperators
def _ThesisExpectedTypes.type_45 : Prop := (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (rp rn : Row m) (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ),
 ∀ᵐ x : Vec n,
 (∀ q ∈ net.absoluteQSources x (fun _ => 0), HasFDerivAt q.value q.jacobian x) ∧
HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1)
 ((1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac - (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x ∧
 HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2)
 ((-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac + (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x)
theorem _ThesisExactChecks.target_45 : _ThesisExpectedTypes.type_45 := by exact @HiddenMonotonicity.Network.affine_plain_Q_gradients_ae
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_plain_Q_gradients_ae
  let expected ← getConstInfo `_ThesisExactChecks.target_45
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_plain_Q_gradients_ae"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_plain_Q_gradients_ae | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.DifferentiableBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_plain_Q_gradients_ae"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_45) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_plain_Q_gradients_ae: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_plain_Q_gradients_ae"
#check @HiddenMonotonicity.Network.affine_plain_Q_gradients_ae
#print axioms _ThesisExactChecks.target_45

section
open HiddenMonotonicity MeasureTheory
open scoped BigOperators
def _ThesisExpectedTypes.type_46 : Prop := (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (x : Vec n) (rp rn : Row m) (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ)
 (hg : DifferentiableAt ℝ (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1) x)
 (hh : DifferentiableAt ℝ (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2) x),
HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1)
 ((1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac - (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x ∧
 HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2)
 ((-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac + (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x)
theorem _ThesisExactChecks.target_46 : _ThesisExpectedTypes.type_46 := by exact @HiddenMonotonicity.Network.affine_plain_formulas_of_differentiable
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_plain_formulas_of_differentiable
  let expected ← getConstInfo `_ThesisExactChecks.target_46
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_plain_formulas_of_differentiable"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_plain_formulas_of_differentiable | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.DifferentiableBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_plain_formulas_of_differentiable"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_46) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_plain_formulas_of_differentiable: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_plain_formulas_of_differentiable"
#check @HiddenMonotonicity.Network.affine_plain_formulas_of_differentiable
#print axioms _ThesisExactChecks.target_46

section
open Thesis.RoutingGate
def _ThesisExpectedTypes.type_47 : Prop := (∀ (z : ℝ),
    chosenLogAction z = decide (0 < z))
theorem _ThesisExactChecks.target_47 : _ThesisExpectedTypes.type_47 := by exact @Thesis.RoutingGate.chosenLogAction_eq_positive
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.chosenLogAction_eq_positive
  let expected ← getConstInfo `_ThesisExactChecks.target_47
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.chosenLogAction_eq_positive"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.chosenLogAction_eq_positive | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.chosenLogAction_eq_positive"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_47) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingGate.chosenLogAction_eq_positive: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.chosenLogAction_eq_positive"
#check @Thesis.RoutingGate.chosenLogAction_eq_positive
#print axioms _ThesisExactChecks.target_47

section
open Thesis.RoutingGate
def _ThesisExpectedTypes.type_48 : Prop := (∀ (z : ℝ) (cont : Bool),
    logAction z cont ≤ logAction z (chosenLogAction z))
theorem _ThesisExactChecks.target_48 : _ThesisExpectedTypes.type_48 := by exact @Thesis.RoutingGate.chosenLogAction_optimal
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.chosenLogAction_optimal
  let expected ← getConstInfo `_ThesisExactChecks.target_48
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.chosenLogAction_optimal"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.chosenLogAction_optimal | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.chosenLogAction_optimal"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_48) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingGate.chosenLogAction_optimal: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.chosenLogAction_optimal"
#check @Thesis.RoutingGate.chosenLogAction_optimal
#print axioms _ThesisExactChecks.target_48

section
open Thesis.RoutingGate
def _ThesisExpectedTypes.type_49 : Prop := (∀ (z : ℝ) (hz : z ≤ 0),
    chosenLogAction z = false)
theorem _ThesisExactChecks.target_49 : _ThesisExpectedTypes.type_49 := by exact @Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive
  let expected ← getConstInfo `_ThesisExactChecks.target_49
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_49) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive"
#check @Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive
#print axioms _ThesisExactChecks.target_49

section
open Thesis.RoutingGate
def _ThesisExpectedTypes.type_50 : Prop := (∀ (z : ℝ),
    (if chosenLogAction z then z else 0) = max z 0)
theorem _ThesisExactChecks.target_50 : _ThesisExpectedTypes.type_50 := by exact @Thesis.RoutingGate.chosenLogAction_mass
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.chosenLogAction_mass
  let expected ← getConstInfo `_ThesisExactChecks.target_50
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.chosenLogAction_mass"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.chosenLogAction_mass | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.chosenLogAction_mass"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_50) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingGate.chosenLogAction_mass: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.chosenLogAction_mass"
#check @Thesis.RoutingGate.chosenLogAction_mass
#print axioms _ThesisExactChecks.target_50

section
open Thesis.RoutingGate
def _ThesisExpectedTypes.type_51 : Prop := (∀ (z : ℝ) (hz : z ≤ 0) (cont : Bool),
    logAction z cont = ⊥)
theorem _ThesisExactChecks.target_51 : _ThesisExpectedTypes.type_51 := by exact @Thesis.RoutingGate.nonpositive_log_actions_tied
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.nonpositive_log_actions_tied
  let expected ← getConstInfo `_ThesisExactChecks.target_51
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.nonpositive_log_actions_tied"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.nonpositive_log_actions_tied | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.nonpositive_log_actions_tied"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_51) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingGate.nonpositive_log_actions_tied: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.nonpositive_log_actions_tied"
#check @Thesis.RoutingGate.nonpositive_log_actions_tied
#print axioms _ThesisExactChecks.target_51

section
open Thesis.RoutingGate
def _ThesisExpectedTypes.type_52 : Prop := (∀ (z : ℝ) (hz : 0 < z),
    logAction z false < logAction z true)
theorem _ThesisExactChecks.target_52 : _ThesisExpectedTypes.type_52 := by exact @Thesis.RoutingGate.positive_continue_strictly_better
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.positive_continue_strictly_better
  let expected ← getConstInfo `_ThesisExactChecks.target_52
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.positive_continue_strictly_better"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.positive_continue_strictly_better | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.positive_continue_strictly_better"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_52) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingGate.positive_continue_strictly_better: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.positive_continue_strictly_better"
#check @Thesis.RoutingGate.positive_continue_strictly_better
#print axioms _ThesisExactChecks.target_52

section
open Thesis.RoutingGate
def _ThesisExpectedTypes.type_53 : Prop := (∀ (z : ℝ) (p : Set.Icc (0 : ℝ) 1),
    logPolicy z p ≤ logPolicy z (chosenLogPolicy z))
theorem _ThesisExactChecks.target_53 : _ThesisExpectedTypes.type_53 := by exact @Thesis.RoutingGate.chosenLogPolicy_optimal
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.chosenLogPolicy_optimal
  let expected ← getConstInfo `_ThesisExactChecks.target_53
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.chosenLogPolicy_optimal"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.chosenLogPolicy_optimal | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.chosenLogPolicy_optimal"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_53) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingGate.chosenLogPolicy_optimal: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.chosenLogPolicy_optimal"
#check @Thesis.RoutingGate.chosenLogPolicy_optimal
#print axioms _ThesisExactChecks.target_53

section
open Thesis.RoutingGate
def _ThesisExpectedTypes.type_54 : Prop := (∀ (z : ℝ) (hz : z ≤ 0)
    (p : Set.Icc (0 : ℝ) 1),
    logPolicy z p = ⊥)
theorem _ThesisExactChecks.target_54 : _ThesisExpectedTypes.type_54 := by exact @Thesis.RoutingGate.nonpositive_log_policies_tied
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.nonpositive_log_policies_tied
  let expected ← getConstInfo `_ThesisExactChecks.target_54
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.nonpositive_log_policies_tied"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.nonpositive_log_policies_tied | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.nonpositive_log_policies_tied"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_54) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingGate.nonpositive_log_policies_tied: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.nonpositive_log_policies_tied"
#check @Thesis.RoutingGate.nonpositive_log_policies_tied
#print axioms _ThesisExactChecks.target_54

section
open Thesis.RoutingGate
def _ThesisExpectedTypes.type_55 : Prop := (∀ (z : ℝ) (hz : 0 < z)
    (p : Set.Icc (0 : ℝ) 1) (hp : p.val < 1),
    logPolicy z p < logPolicy z (chosenLogPolicy z))
theorem _ThesisExactChecks.target_55 : _ThesisExpectedTypes.type_55 := by exact @Thesis.RoutingGate.positive_log_policy_strict
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.positive_log_policy_strict
  let expected ← getConstInfo `_ThesisExactChecks.target_55
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.positive_log_policy_strict"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.positive_log_policy_strict | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.positive_log_policy_strict"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_55) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingGate.positive_log_policy_strict: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.positive_log_policy_strict"
#check @Thesis.RoutingGate.positive_log_policy_strict
#print axioms _ThesisExactChecks.target_55

section
open Thesis.RoutingGate
def _ThesisExpectedTypes.type_56 : Prop := (∀ (c z : ℝ),
    HasDerivAt (frozenGate c) c z)
theorem _ThesisExactChecks.target_56 : _ThesisExpectedTypes.type_56 := by exact @Thesis.RoutingGate.frozenGate_hasDerivAt
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.frozenGate_hasDerivAt
  let expected ← getConstInfo `_ThesisExactChecks.target_56
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.frozenGate_hasDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.frozenGate_hasDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.frozenGate_hasDerivAt"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_56) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingGate.frozenGate_hasDerivAt: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.frozenGate_hasDerivAt"
#check @Thesis.RoutingGate.frozenGate_hasDerivAt
#print axioms _ThesisExactChecks.target_56

section
open Thesis.RoutingGate
def _ThesisExpectedTypes.type_57 : Prop := (∀ (c z : ℝ) (hc : 0 ≤ c) (hz : 0 ≤ z),
    0 ≤ frozenGate c z)
theorem _ThesisExactChecks.target_57 : _ThesisExpectedTypes.type_57 := by exact @Thesis.RoutingGate.frozenGate_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.frozenGate_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_57
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.frozenGate_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.frozenGate_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.frozenGate_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_57) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingGate.frozenGate_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.frozenGate_nonnegative"
#check @Thesis.RoutingGate.frozenGate_nonnegative
#print axioms _ThesisExactChecks.target_57

section
open Thesis.RoutingGate
def _ThesisExpectedTypes.type_58 : Prop := (∀ (g : ℝ → ℝ) (z d : ℝ) (hg : HasDerivAt g d z),
    HasDerivAt (fun y => g y * y) (g z + z*d) z)
theorem _ThesisExactChecks.target_58 : _ThesisExpectedTypes.type_58 := by exact @Thesis.RoutingGate.varyingGate_hasDerivAt
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.varyingGate_hasDerivAt
  let expected ← getConstInfo `_ThesisExactChecks.target_58
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.varyingGate_hasDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.varyingGate_hasDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.varyingGate_hasDerivAt"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_58) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingGate.varyingGate_hasDerivAt: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.varyingGate_hasDerivAt"
#check @Thesis.RoutingGate.varyingGate_hasDerivAt
#print axioms _ThesisExactChecks.target_58

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition Thesis.StoppingBoundary
def _ThesisExpectedTypes.type_59 : Prop := (∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (g : Fin k → Bool) (j : Fin k) (turn : Bool),
    (∑ target, transition wp wn g j turn target) = 1)
theorem _ThesisExactChecks.target_59 : _ThesisExpectedTypes.type_59 := by exact @Thesis.StoppingBoundary.transition_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingBoundary.transition_normalized
  let expected ← getConstInfo `_ThesisExactChecks.target_59
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingBoundary.transition_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingBoundary.transition_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingBoundary do
    throwError "Defining module mismatch: Thesis.StoppingBoundary.transition_normalized"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_59) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingBoundary.transition_normalized: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingBoundary.transition_normalized"
#check @Thesis.StoppingBoundary.transition_normalized
#print axioms _ThesisExactChecks.target_59

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition Thesis.StoppingBoundary
def _ThesisExpectedTypes.type_60 : Prop := (∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (g : Fin k → Bool) (hw : ∀ j i, 0 ≤ wp j i ∧ 0 ≤ wn j i)
    (j : Fin k) (turn : Bool) (target : Option (Fin n × Bool)),
    0 ≤ transition wp wn g j turn target)
theorem _ThesisExactChecks.target_60 : _ThesisExpectedTypes.type_60 := by exact @Thesis.StoppingBoundary.transition_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingBoundary.transition_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_60
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingBoundary.transition_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingBoundary.transition_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingBoundary do
    throwError "Defining module mismatch: Thesis.StoppingBoundary.transition_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_60) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingBoundary.transition_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingBoundary.transition_nonnegative"
#check @Thesis.StoppingBoundary.transition_nonnegative
#print axioms _ThesisExactChecks.target_60

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition Thesis.StoppingBoundary
def _ThesisExpectedTypes.type_61 : Prop := (∀ {n m} (tr : MaskedTrace n m)
    (hw : NonnegativeWeights tr) (j : Fin m) (i : Fin n) (p : Bool) (path : Paths tr),
    sgDiscount tr path * sgProbability tr j i p path = rawWeight tr j i p path)
theorem _ThesisExactChecks.target_61 : _ThesisExpectedTypes.type_61 := by exact @Thesis.StoppingBoundary.path_discount_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingBoundary.path_discount_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_61
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingBoundary.path_discount_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingBoundary.path_discount_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingBoundary do
    throwError "Defining module mismatch: Thesis.StoppingBoundary.path_discount_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_61) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingBoundary.path_discount_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingBoundary.path_discount_recovery"
#check @Thesis.StoppingBoundary.path_discount_recovery
#print axioms _ThesisExactChecks.target_61

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition Thesis.StoppingBoundary
def _ThesisExpectedTypes.type_62 : Prop := (∀ {n m} (tr : MaskedTrace n m) (hw : NonnegativeWeights tr)
    (j : Fin m) (i : Fin n),
    tr.originalJac (Pi.single i 1) j = sgOccupation tr j i false - sgOccupation tr j i true)
theorem _ThesisExactChecks.target_62 : _ThesisExpectedTypes.type_62 := by exact @Thesis.StoppingBoundary.selected_operator_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingBoundary.selected_operator_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_62
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingBoundary.selected_operator_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingBoundary.selected_operator_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingBoundary do
    throwError "Defining module mismatch: Thesis.StoppingBoundary.selected_operator_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_62) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingBoundary.selected_operator_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingBoundary.selected_operator_occupation"
#check @Thesis.StoppingBoundary.selected_operator_occupation
#print axioms _ThesisExactChecks.target_62

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition Thesis.StoppingBoundary
def _ThesisExpectedTypes.type_63 : Prop := (∀ {n m} (net : Network n m) (x : Vec n)
    (hx : net.Strict x) (hw : NonnegativeWeights (net.originalTrace x))
    (j : Fin m) (i : Fin n),
    fderiv ℝ net.eval x (Pi.single i 1) j =
      sgOccupation (net.originalTrace x) j i false - sgOccupation (net.originalTrace x) j i true)
theorem _ThesisExactChecks.target_63 : _ThesisExpectedTypes.type_63 := by exact @Thesis.StoppingBoundary.strict_gradient_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingBoundary.strict_gradient_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_63
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingBoundary.strict_gradient_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingBoundary.strict_gradient_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingBoundary do
    throwError "Defining module mismatch: Thesis.StoppingBoundary.strict_gradient_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_63) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingBoundary.strict_gradient_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingBoundary.strict_gradient_occupation"
#check @Thesis.StoppingBoundary.strict_gradient_occupation
#print axioms _ThesisExactChecks.target_63

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition Thesis.StoppingBoundary
def _ThesisExpectedTypes.type_64 : Prop := (∀ {n m} (net : Network n m)
    (x : PairVec n) (hx : net.Strict (x.1-x.2))
    (hw : NonnegativeWeights (net.originalTrace (x.1-x.2))) (j : Fin m) (i : Fin n),
    (fderiv ℝ (net.decomposeWith stopPair) x (Pi.single i 1,0)).1 j =
      sgOccupation (net.originalTrace (x.1-x.2)) j i false ∧
    (fderiv ℝ (net.decomposeWith stopPair) x (Pi.single i 1,0)).2 j =
      sgOccupation (net.originalTrace (x.1-x.2)) j i true)
theorem _ThesisExactChecks.target_64 : _ThesisExpectedTypes.type_64 := by exact @Thesis.StoppingBoundary.strict_stopping_decomposition_gradient
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingBoundary.strict_stopping_decomposition_gradient
  let expected ← getConstInfo `_ThesisExactChecks.target_64
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingBoundary.strict_stopping_decomposition_gradient"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingBoundary.strict_stopping_decomposition_gradient | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingBoundary do
    throwError "Defining module mismatch: Thesis.StoppingBoundary.strict_stopping_decomposition_gradient"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_64) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingBoundary.strict_stopping_decomposition_gradient: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingBoundary.strict_stopping_decomposition_gradient"
#check @Thesis.StoppingBoundary.strict_stopping_decomposition_gradient
#print axioms _ThesisExactChecks.target_64

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition Thesis.StoppingBoundary
def _ThesisExpectedTypes.type_65 : Prop := (∀ {n m r} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (x : Vec n) (hx : net.Strict x)
    (hw : NonnegativeWeights (net.originalTrace x)) (u : Fin r) (i : Fin n),
    fderiv ℝ (Thesis.AffineOutputBackward.affineOutput net C b) x (Pi.single i 1) u =
      ∑ j, C u j * (sgOccupation (net.originalTrace x) j i false -
        sgOccupation (net.originalTrace x) j i true))
theorem _ThesisExactChecks.target_65 : _ThesisExpectedTypes.type_65 := by exact @Thesis.StoppingBoundary.strict_affine_output_gradient
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingBoundary.strict_affine_output_gradient
  let expected ← getConstInfo `_ThesisExactChecks.target_65
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingBoundary.strict_affine_output_gradient"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingBoundary.strict_affine_output_gradient | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingBoundary do
    throwError "Defining module mismatch: Thesis.StoppingBoundary.strict_affine_output_gradient"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_65) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingBoundary.strict_affine_output_gradient: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingBoundary.strict_affine_output_gradient"
#check @Thesis.StoppingBoundary.strict_affine_output_gradient
#print axioms _ThesisExactChecks.target_65

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.SoftplusBackward Thesis.Regularization Thesis.SoftplusBoundary
def _ThesisExpectedTypes.type_66 : Prop := (∀ {n k} (θ z : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (j : Fin k) (turn : Bool),
    (∑ target, transition θ z wp wn j turn target) = 1)
theorem _ThesisExactChecks.target_66 : _ThesisExpectedTypes.type_66 := by exact @Thesis.SoftplusBoundary.transition_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusBoundary.transition_normalized
  let expected ← getConstInfo `_ThesisExactChecks.target_66
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusBoundary.transition_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusBoundary.transition_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusBoundary do
    throwError "Defining module mismatch: Thesis.SoftplusBoundary.transition_normalized"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_66) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusBoundary.transition_normalized: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusBoundary.transition_normalized"
#check @Thesis.SoftplusBoundary.transition_normalized
#print axioms _ThesisExactChecks.target_66

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.SoftplusBackward Thesis.Regularization Thesis.SoftplusBoundary
def _ThesisExpectedTypes.type_67 : Prop := (∀ {n k} (θ z : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hw : ∀ j i, 0 ≤ wp j i ∧ 0 ≤ wn j i)
    (j : Fin k) (turn : Bool) (target : Option (Fin n × Bool)),
    0 ≤ transition θ z wp wn j turn target)
theorem _ThesisExactChecks.target_67 : _ThesisExpectedTypes.type_67 := by exact @Thesis.SoftplusBoundary.transition_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusBoundary.transition_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_67
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusBoundary.transition_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusBoundary.transition_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusBoundary do
    throwError "Defining module mismatch: Thesis.SoftplusBoundary.transition_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_67) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusBoundary.transition_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusBoundary.transition_nonnegative"
#check @Thesis.SoftplusBoundary.transition_nonnegative
#print axioms _ThesisExactChecks.target_67

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.SoftplusBackward Thesis.Regularization Thesis.SoftplusBoundary
def _ThesisExpectedTypes.type_68 : Prop := (∀ {n k} (θ z : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (j : Fin k) (turn : Bool) (hz : fanIn wp wn j = 0),
    transition θ z wp wn j turn none = 1)
theorem _ThesisExactChecks.target_68 : _ThesisExpectedTypes.type_68 := by exact @Thesis.SoftplusBoundary.zero_fanIn_absorbs
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusBoundary.zero_fanIn_absorbs
  let expected ← getConstInfo `_ThesisExactChecks.target_68
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusBoundary.zero_fanIn_absorbs"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusBoundary.zero_fanIn_absorbs | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusBoundary do
    throwError "Defining module mismatch: Thesis.SoftplusBoundary.zero_fanIn_absorbs"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_68) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusBoundary.zero_fanIn_absorbs: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusBoundary.zero_fanIn_absorbs"
#check @Thesis.SoftplusBoundary.zero_fanIn_absorbs
#print axioms _ThesisExactChecks.target_68

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.SoftplusBackward Thesis.Regularization Thesis.SoftplusBoundary
def _ThesisExpectedTypes.type_69 : Prop := (∀ {n m} (net : Network n m) (θ : ℝ) (hθ : 0 < θ)
    (hw : net.Nonnegative) (x : Vec n) (j : Fin m) (i : Fin n),
    fderiv ℝ (softEval θ net) x (Pi.single i 1) j =
      softOccupation net θ x j i false - softOccupation net θ x j i true)
theorem _ThesisExactChecks.target_69 : _ThesisExpectedTypes.type_69 := by exact @Thesis.SoftplusBoundary.gradient_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusBoundary.gradient_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_69
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusBoundary.gradient_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusBoundary.gradient_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusBoundary do
    throwError "Defining module mismatch: Thesis.SoftplusBoundary.gradient_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_69) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusBoundary.gradient_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusBoundary.gradient_occupation"
#check @Thesis.SoftplusBoundary.gradient_occupation
#print axioms _ThesisExactChecks.target_69

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingSupport
def _ThesisExpectedTypes.type_70 : Prop := (∀ {n m} (net : Network n m) (α β ε : ℝ)
    (x : Vec n) (R : Vec m) (hR : ∀ j, net.eval x j = 0 → R j = 0),
    sourceLRP α β ε net x R = lrp α β ε net x R)
theorem _ThesisExactChecks.target_70 : _ThesisExpectedTypes.type_70 := by exact @Thesis.RoutingSupport.sourceLRP_eq_lrp
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingSupport.sourceLRP_eq_lrp
  let expected ← getConstInfo `_ThesisExactChecks.target_70
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingSupport.sourceLRP_eq_lrp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingSupport.sourceLRP_eq_lrp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingSupport do
    throwError "Defining module mismatch: Thesis.RoutingSupport.sourceLRP_eq_lrp"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_70) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingSupport.sourceLRP_eq_lrp: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingSupport.sourceLRP_eq_lrp"
#check @Thesis.RoutingSupport.sourceLRP_eq_lrp
#print axioms _ThesisExactChecks.target_70

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingSupport
def _ThesisExpectedTypes.type_71 : Prop := (∀ {n m} (net : Network n m) (α β ε : ℝ)
    (x : Vec n) (R : Vec m) (hR : ∀ j, net.eval x j = 0 → R j = 0) (i : Fin n),
    sourceLRP α β ε net x R i = ∑ j, R j *
      (rgOccupation net α β ε x j i false - rgOccupation net α β ε x j i true))
theorem _ThesisExactChecks.target_71 : _ThesisExpectedTypes.type_71 := by exact @Thesis.RoutingSupport.source_alpha_beta_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingSupport.source_alpha_beta_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_71
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingSupport.source_alpha_beta_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingSupport.source_alpha_beta_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingSupport do
    throwError "Defining module mismatch: Thesis.RoutingSupport.source_alpha_beta_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_71) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingSupport.source_alpha_beta_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingSupport.source_alpha_beta_recovery"
#check @Thesis.RoutingSupport.source_alpha_beta_recovery
#print axioms _ThesisExactChecks.target_71

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingSupport
def _ThesisExpectedTypes.type_72 : Prop := (∀ {n m} (net : Network n m) (α β ε : ℝ)
    (x : Vec n) (i : Fin n),
    sourceLRP α β ε net x (net.eval x) i = ∑ j, net.eval x j *
      (rgOccupation net α β ε x j i false - rgOccupation net α β ε x j i true))
theorem _ThesisExactChecks.target_72 : _ThesisExpectedTypes.type_72 := by exact @Thesis.RoutingSupport.source_alpha_beta_output_seed
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingSupport.source_alpha_beta_output_seed
  let expected ← getConstInfo `_ThesisExactChecks.target_72
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingSupport.source_alpha_beta_output_seed"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingSupport.source_alpha_beta_output_seed | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingSupport do
    throwError "Defining module mismatch: Thesis.RoutingSupport.source_alpha_beta_output_seed"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_72) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingSupport.source_alpha_beta_output_seed: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingSupport.source_alpha_beta_output_seed"
#check @Thesis.RoutingSupport.source_alpha_beta_output_seed
#print axioms _ThesisExactChecks.target_72

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingSupport
def _ThesisExpectedTypes.type_73 : Prop := (∀ {n m r} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ) (x : Vec n) (R : Vec r),
    sourceAffineOutputLRP net C b α β ε x R =
      Thesis.AffineOutputBackward.affineOutputLRP net C b α β ε x R)
theorem _ThesisExactChecks.target_73 : _ThesisExpectedTypes.type_73 := by exact @Thesis.RoutingSupport.sourceAffineOutputLRP_eq
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingSupport.sourceAffineOutputLRP_eq
  let expected ← getConstInfo `_ThesisExactChecks.target_73
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingSupport.sourceAffineOutputLRP_eq"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingSupport.sourceAffineOutputLRP_eq | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingSupport do
    throwError "Defining module mismatch: Thesis.RoutingSupport.sourceAffineOutputLRP_eq"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_73) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingSupport.sourceAffineOutputLRP_eq: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingSupport.sourceAffineOutputLRP_eq"
#check @Thesis.RoutingSupport.sourceAffineOutputLRP_eq
#print axioms _ThesisExactChecks.target_73

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingSupport
def _ThesisExpectedTypes.type_74 : Prop := (∀ {n m r} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ)
    (x : Vec n) (R : Vec r) (i : Fin n),
    sourceAffineOutputLRP net C b α β ε x R i = ∑ u, R u *
      (Thesis.AffineOutputBackward.readoutOccupation net C b α β ε x u i false -
       Thesis.AffineOutputBackward.readoutOccupation net C b α β ε x u i true))
theorem _ThesisExactChecks.target_74 : _ThesisExpectedTypes.type_74 := by exact @Thesis.RoutingSupport.source_affine_output_lrp
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingSupport.source_affine_output_lrp
  let expected ← getConstInfo `_ThesisExactChecks.target_74
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingSupport.source_affine_output_lrp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingSupport.source_affine_output_lrp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingSupport do
    throwError "Defining module mismatch: Thesis.RoutingSupport.source_affine_output_lrp"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_74) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingSupport.source_affine_output_lrp: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingSupport.source_affine_output_lrp"
#check @Thesis.RoutingSupport.source_affine_output_lrp
#print axioms _ThesisExactChecks.target_74

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.RoutingTransitions
def _ThesisExpectedTypes.type_75 : Prop := (∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (x : Vec n) (j : Fin k) (turn : Bool),
    (∑ target, transition wp wn bp bn ε x j turn target) = 1)
theorem _ThesisExactChecks.target_75 : _ThesisExpectedTypes.type_75 := by exact @Thesis.RoutingTransitions.transition_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingTransitions.transition_normalized
  let expected ← getConstInfo `_ThesisExactChecks.target_75
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingTransitions.transition_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingTransitions.transition_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingTransitions do
    throwError "Defining module mismatch: Thesis.RoutingTransitions.transition_normalized"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_75) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingTransitions.transition_normalized: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingTransitions.transition_normalized"
#check @Thesis.RoutingTransitions.transition_normalized
#print axioms _ThesisExactChecks.target_75

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.RoutingTransitions
def _ThesisExpectedTypes.type_76 : Prop := (∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k)
    (turn : Bool) (target : Option (Fin n × Bool)),
    0 ≤ transition wp wn bp bn ε x j turn target)
theorem _ThesisExactChecks.target_76 : _ThesisExpectedTypes.type_76 := by exact @Thesis.RoutingTransitions.transition_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingTransitions.transition_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_76
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingTransitions.transition_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingTransitions.transition_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingTransitions do
    throwError "Defining module mismatch: Thesis.RoutingTransitions.transition_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_76) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingTransitions.transition_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingTransitions.transition_nonnegative"
#check @Thesis.RoutingTransitions.transition_nonnegative
#print axioms _ThesisExactChecks.target_76

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.RoutingTransitions
def _ThesisExpectedTypes.type_77 : Prop := (∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (x : Vec n) (j : Fin k) (turn p : Bool) (i : Fin n),
    transition wp wn bp bn ε x j turn (some (i,p)) =
      if 0 < preactivation wp wn bp bn x j then
        (if p = turn then posContribution wp wn x j i / posDenominator wp wn bp bn ε x j
         else negContribution wp wn x j i / negDenominator wp wn bp bn ε x j) / 2 else 0)
theorem _ThesisExactChecks.target_77 : _ThesisExpectedTypes.type_77 := by exact @Thesis.RoutingTransitions.transition_ordinary
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingTransitions.transition_ordinary
  let expected ← getConstInfo `_ThesisExactChecks.target_77
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingTransitions.transition_ordinary"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingTransitions.transition_ordinary | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingTransitions do
    throwError "Defining module mismatch: Thesis.RoutingTransitions.transition_ordinary"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_77) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingTransitions.transition_ordinary: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingTransitions.transition_ordinary"
#check @Thesis.RoutingTransitions.transition_ordinary
#print axioms _ThesisExactChecks.target_77

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.RoutingTransitions
def _ThesisExpectedTypes.type_78 : Prop := (∀ {n m} (net : Network n m) (α β ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (i : Fin n) (p : Bool)
    (path : Paths (routingTrace α β ε net x)),
    0 ≤ rgProbability α β ε net x j i p path)
theorem _ThesisExactChecks.target_78 : _ThesisExpectedTypes.type_78 := by exact @Thesis.RoutingTransitions.probability_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingTransitions.probability_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_78
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingTransitions.probability_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingTransitions.probability_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingTransitions do
    throwError "Defining module mismatch: Thesis.RoutingTransitions.probability_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_78) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingTransitions.probability_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingTransitions.probability_nonnegative"
#check @Thesis.RoutingTransitions.probability_nonnegative
#print axioms _ThesisExactChecks.target_78

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.RoutingTransitions
def _ThesisExpectedTypes.type_79 : Prop := (∀ {n m} (net : Network n m) (α β ε : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : 0 ≤ ε) (x : Vec n)
    (j : Fin m) (i : Fin n) (p : Bool),
    0 ≤ rgOccupation net α β ε x j i p)
theorem _ThesisExactChecks.target_79 : _ThesisExpectedTypes.type_79 := by exact @Thesis.RoutingTransitions.occupation_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingTransitions.occupation_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_79
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingTransitions.occupation_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingTransitions.occupation_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingTransitions do
    throwError "Defining module mismatch: Thesis.RoutingTransitions.occupation_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_79) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingTransitions.occupation_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingTransitions.occupation_nonnegative"
#check @Thesis.RoutingTransitions.occupation_nonnegative
#print axioms _ThesisExactChecks.target_79

section
universe u
open MeasureTheory Filter Finset Thesis.Games Thesis.Randomization Thesis.RandomizationExpectation Thesis.RoutingExpectation
open scoped MeasureTheory
def _ThesisExpectedTypes.type_80 : Prop := (∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] {S : Type} [Fintype S] [DecidableEq S] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : ℕ → MeasurableSpace Ω) (hm : ∀ n, ℱ n ≤ mΩ)
    (A : ℕ → S → S → ℝ) (B : ℕ → Ω → S → S → ℝ) (s₀ : S)
    (b : ℝ) (hb : 0 ≤ b)
    (hg : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (ha : ∀ n s, Integrable (rowAffinity A B n s) μ)
    (hga : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s *
      rowAffinity A B n s ω) μ)
    (hgm : ∀ n s, AEStronglyMeasurable[ℱ n]
      (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (n : ℕ) (hcond : ∀ l < n, ∀ s, ∀ᵐ ω ∂μ, μ[rowAffinity A B l s | ℱ l] ω ≤ b),
    (∫ ω, ordinaryOverlap n A (fun l => B l ω) s₀ ∂μ) ≤ b^n)
theorem _ThesisExactChecks.target_80 : _ThesisExpectedTypes.type_80.{u} := by exact @Thesis.RoutingExpectation.conditional_affinity_contraction.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExpectation.conditional_affinity_contraction
  let expected ← getConstInfo `_ThesisExactChecks.target_80
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExpectation.conditional_affinity_contraction"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExpectation.conditional_affinity_contraction | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExpectation do
    throwError "Defining module mismatch: Thesis.RoutingExpectation.conditional_affinity_contraction"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_80) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingExpectation.conditional_affinity_contraction: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExpectation.conditional_affinity_contraction"
#check @Thesis.RoutingExpectation.conditional_affinity_contraction
#print axioms _ThesisExactChecks.target_80

section
universe u
open MeasureTheory Filter Finset Thesis.Games Thesis.Randomization Thesis.RandomizationExpectation Thesis.RoutingExpectation
open scoped MeasureTheory
def _ThesisExpectedTypes.type_81 : Prop := (∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] {S : Type} [Fintype S] [DecidableEq S] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : ℕ → MeasurableSpace Ω) (hm : ∀ n, ℱ n ≤ mΩ)
    (A : ℕ → S → S → ℝ) (B : ℕ → Ω → S → S → ℝ) (s₀ : S)
    (b : ℝ) (hb : 0 ≤ b)
    (hA : ∀ n s t, 0 ≤ A n s t) (hB : ∀ n ω s t, 0 ≤ B n ω s t)
    (hArow : ∀ n s, ∑ t, A n s t ≤ 1) (hBrow : ∀ n ω s, ∑ t, B n ω s t ≤ 1)
    (hg : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (ha : ∀ n s, Integrable (rowAffinity A B n s) μ)
    (hga : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s *
      rowAffinity A B n s ω) μ)
    (hgm : ∀ n s, AEStronglyMeasurable[ℱ n]
      (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (n extra : ℕ)
    (hcond : ∀ l < n, ∀ s, ∀ᵐ ω ∂μ, μ[rowAffinity A B l s | ℱ l] ω ≤ b),
    (∫ ω, ordinaryOverlap (n+extra) A (fun l => B l ω) s₀ ∂μ) ≤ b^n)
theorem _ThesisExactChecks.target_81 : _ThesisExpectedTypes.type_81.{u} := by exact @Thesis.RoutingExpectation.conditional_affinity_full_depth.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExpectation.conditional_affinity_full_depth
  let expected ← getConstInfo `_ThesisExactChecks.target_81
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExpectation.conditional_affinity_full_depth"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExpectation.conditional_affinity_full_depth | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExpectation do
    throwError "Defining module mismatch: Thesis.RoutingExpectation.conditional_affinity_full_depth"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_81) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingExpectation.conditional_affinity_full_depth: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExpectation.conditional_affinity_full_depth"
#check @Thesis.RoutingExpectation.conditional_affinity_full_depth
#print axioms _ThesisExactChecks.target_81

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames
def _ThesisExpectedTypes.type_82 : Prop := (∀ {n m} (net : Network n m) (x : Vec n)
    (hx : net.Regular (x,0)) (hγ : PositiveFanIn (net.trace (x,0))),
    HasFDerivAt net.eval (matrixCLM (fun j i =>
      sgOccupation (net.trace (x,0)) j i false -
      sgOccupation (net.trace (x,0)) j i true)) x)
theorem _ThesisExactChecks.target_82 : _ThesisExpectedTypes.type_82 := by exact @Thesis.BackwardGames.stopping_game_gradient
end
run_cmd do
  let target ← getConstInfo `Thesis.BackwardGames.stopping_game_gradient
  let expected ← getConstInfo `_ThesisExactChecks.target_82
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.BackwardGames.stopping_game_gradient"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.BackwardGames.stopping_game_gradient | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.BackwardGames do
    throwError "Defining module mismatch: Thesis.BackwardGames.stopping_game_gradient"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_82) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.BackwardGames.stopping_game_gradient: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.BackwardGames.stopping_game_gradient"
#check @Thesis.BackwardGames.stopping_game_gradient
#print axioms _ThesisExactChecks.target_82

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames
def _ThesisExpectedTypes.type_83 : Prop := (∀ {n m} (net : Network n m) (x : Vec n)
    (hx : net.Regular (x,0)) (hγ : PositiveFanIn (net.trace (x,0)))
    (_hw : NonnegativeWeights (net.trace (x,0)))
    (j : Fin m) (i : Fin n),
    fderiv ℝ net.eval x (Pi.single i 1) j =
      sgOccupation (net.trace (x,0)) j i false - sgOccupation (net.trace (x,0)) j i true)
theorem _ThesisExactChecks.target_83 : _ThesisExpectedTypes.type_83 := by exact @Thesis.BackwardGames.thesis_gradient_representation
end
run_cmd do
  let target ← getConstInfo `Thesis.BackwardGames.thesis_gradient_representation
  let expected ← getConstInfo `_ThesisExactChecks.target_83
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.BackwardGames.thesis_gradient_representation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.BackwardGames.thesis_gradient_representation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.BackwardGames do
    throwError "Defining module mismatch: Thesis.BackwardGames.thesis_gradient_representation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_83) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.BackwardGames.thesis_gradient_representation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.BackwardGames.thesis_gradient_representation"
#check @Thesis.BackwardGames.thesis_gradient_representation
#print axioms _ThesisExactChecks.target_83

section
open HiddenMonotonicity Matrix Finset Filter Thesis.BackwardGames Thesis.StoppingDecomposition
open scoped Topology
def _ThesisExpectedTypes.type_84 : Prop := (∀ {n m} (net : Network n m) (x : PairVec n),
    (net.decomposeWith stopPair x).1 - (net.decomposeWith stopPair x).2 = net.eval (x.1-x.2))
theorem _ThesisExactChecks.target_84 : _ThesisExpectedTypes.type_84 := by exact @Thesis.StoppingDecomposition.thesis_stopping_validity
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDecomposition.thesis_stopping_validity
  let expected ← getConstInfo `_ThesisExactChecks.target_84
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDecomposition.thesis_stopping_validity"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDecomposition.thesis_stopping_validity | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDecomposition do
    throwError "Defining module mismatch: Thesis.StoppingDecomposition.thesis_stopping_validity"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_84) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDecomposition.thesis_stopping_validity: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDecomposition.thesis_stopping_validity"
#check @Thesis.StoppingDecomposition.thesis_stopping_validity
#print axioms _ThesisExactChecks.target_84

section
open HiddenMonotonicity Matrix Finset Filter Thesis.BackwardGames Thesis.StoppingDecomposition
open scoped Topology
def _ThesisExpectedTypes.type_85 : Prop := (∀ {n m} (net : Network n m)
    (x : PairVec n) (hx : net.Strict (x.1-x.2))
    (hγ : Thesis.BackwardGames.PositiveFanIn (net.originalTrace (x.1-x.2)))
    (j : Fin m) (i : Fin n),
    (fderiv ℝ (net.decomposeWith stopPair) x (Pi.single i 1,0)).1 j =
      sgOccupation (net.originalTrace (x.1-x.2)) j i false ∧
    (fderiv ℝ (net.decomposeWith stopPair) x (Pi.single i 1,0)).2 j =
      sgOccupation (net.originalTrace (x.1-x.2)) j i true)
theorem _ThesisExactChecks.target_85 : _ThesisExpectedTypes.type_85 := by exact @Thesis.StoppingDecomposition.thesis_stopping_decomposition_gradient
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDecomposition.thesis_stopping_decomposition_gradient
  let expected ← getConstInfo `_ThesisExactChecks.target_85
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDecomposition.thesis_stopping_decomposition_gradient"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDecomposition.thesis_stopping_decomposition_gradient | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDecomposition do
    throwError "Defining module mismatch: Thesis.StoppingDecomposition.thesis_stopping_decomposition_gradient"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_85) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDecomposition.thesis_stopping_decomposition_gradient: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDecomposition.thesis_stopping_decomposition_gradient"
#check @Thesis.StoppingDecomposition.thesis_stopping_decomposition_gradient
#print axioms _ThesisExactChecks.target_85

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward
def _ThesisExpectedTypes.type_86 : Prop := (∀ {n m} (net : Network n m) (α β ε : ℝ)
    (x : Vec n) (R : Vec m) (i : Fin n),
    lrp α β ε net x R i = ∑ j, R j *
      (rgOccupation net α β ε x j i false - rgOccupation net α β ε x j i true))
theorem _ThesisExactChecks.target_86 : _ThesisExpectedTypes.type_86 := by exact @Thesis.RoutingBackward.thesis_alpha_beta_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingBackward.thesis_alpha_beta_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_86
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingBackward.thesis_alpha_beta_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingBackward.thesis_alpha_beta_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingBackward do
    throwError "Defining module mismatch: Thesis.RoutingBackward.thesis_alpha_beta_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_86) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingBackward.thesis_alpha_beta_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingBackward.thesis_alpha_beta_recovery"
#check @Thesis.RoutingBackward.thesis_alpha_beta_recovery
#print axioms _ThesisExactChecks.target_86

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.AttentionBackward Thesis.AffineOutputBackward
def _ThesisExpectedTypes.type_87 : Prop := (∀ {n m r} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ)
    (b : Vec r) (x : Vec n) (hx : net.Strict x) (hγ : PositiveFanIn (net.originalTrace x))
    (u : Fin r) (i : Fin n),
    fderiv ℝ (affineOutput net C b) x (Pi.single i 1) u =
      ∑ j, C u j * (sgOccupation (net.originalTrace x) j i false -
        sgOccupation (net.originalTrace x) j i true))
theorem _ThesisExactChecks.target_87 : _ThesisExpectedTypes.type_87 := by exact @Thesis.AffineOutputBackward.thesis_affine_output_gradient
end
run_cmd do
  let target ← getConstInfo `Thesis.AffineOutputBackward.thesis_affine_output_gradient
  let expected ← getConstInfo `_ThesisExactChecks.target_87
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.AffineOutputBackward.thesis_affine_output_gradient"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AffineOutputBackward.thesis_affine_output_gradient | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AffineOutputBackward do
    throwError "Defining module mismatch: Thesis.AffineOutputBackward.thesis_affine_output_gradient"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_87) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AffineOutputBackward.thesis_affine_output_gradient: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AffineOutputBackward.thesis_affine_output_gradient"
#check @Thesis.AffineOutputBackward.thesis_affine_output_gradient
#print axioms _ThesisExactChecks.target_87

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.AttentionBackward Thesis.AffineOutputBackward
def _ThesisExpectedTypes.type_88 : Prop := (∀ {n m r} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ)
    (b : Vec r) (α β ε : ℝ) (x : Vec n) (R : Vec r) (i : Fin n),
    affineOutputLRP net C b α β ε x R i = ∑ u, R u *
      (readoutOccupation net C b α β ε x u i false -
       readoutOccupation net C b α β ε x u i true))
theorem _ThesisExactChecks.target_88 : _ThesisExpectedTypes.type_88 := by exact @Thesis.AffineOutputBackward.thesis_affine_output_lrp
end
run_cmd do
  let target ← getConstInfo `Thesis.AffineOutputBackward.thesis_affine_output_lrp
  let expected ← getConstInfo `_ThesisExactChecks.target_88
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.AffineOutputBackward.thesis_affine_output_lrp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AffineOutputBackward.thesis_affine_output_lrp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AffineOutputBackward do
    throwError "Defining module mismatch: Thesis.AffineOutputBackward.thesis_affine_output_lrp"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_88) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AffineOutputBackward.thesis_affine_output_lrp: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AffineOutputBackward.thesis_affine_output_lrp"
#check @Thesis.AffineOutputBackward.thesis_affine_output_lrp
#print axioms _ThesisExactChecks.target_88

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.Regularization Thesis.SoftplusBackward
def _ThesisExpectedTypes.type_89 : Prop := (∀ {n m} (net : Network n m) (θ : ℝ) (hθ : 0 < θ)
    (_hw : net.Nonnegative) (hγ : PositiveFanIn net) (x : Vec n) (j : Fin m) (i : Fin n),
    fderiv ℝ (softEval θ net) x (Pi.single i 1) j =
      softOccupation net θ x j i false - softOccupation net θ x j i true)
theorem _ThesisExactChecks.target_89 : _ThesisExpectedTypes.type_89 := by exact @Thesis.SoftplusBackward.thesis_softplus_gradient
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusBackward.thesis_softplus_gradient
  let expected ← getConstInfo `_ThesisExactChecks.target_89
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusBackward.thesis_softplus_gradient"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusBackward.thesis_softplus_gradient | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusBackward do
    throwError "Defining module mismatch: Thesis.SoftplusBackward.thesis_softplus_gradient"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_89) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusBackward.thesis_softplus_gradient: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusBackward.thesis_softplus_gradient"
#check @Thesis.SoftplusBackward.thesis_softplus_gradient
#print axioms _ThesisExactChecks.target_89

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.SoftplusDecomposition
def _ThesisExpectedTypes.type_90 : Prop := (∀ {n m} (net : Network n m) (θ : ℝ),
    softEval θ net = net.forwardWith (softplus θ))
theorem _ThesisExactChecks.target_90 : _ThesisExpectedTypes.type_90 := by exact @Thesis.SoftplusDecomposition.softEval_eq_forwardWith
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusDecomposition.softEval_eq_forwardWith
  let expected ← getConstInfo `_ThesisExactChecks.target_90
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusDecomposition.softEval_eq_forwardWith"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusDecomposition.softEval_eq_forwardWith | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusDecomposition do
    throwError "Defining module mismatch: Thesis.SoftplusDecomposition.softEval_eq_forwardWith"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_90) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusDecomposition.softEval_eq_forwardWith: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusDecomposition.softEval_eq_forwardWith"
#check @Thesis.SoftplusDecomposition.softEval_eq_forwardWith
#print axioms _ThesisExactChecks.target_90

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.SoftplusDecomposition
def _ThesisExpectedTypes.type_91 : Prop := (∀ {n m} (net : Network n m) (θ : ℝ) (hθ : 0 < θ)
    (x : PairVec n),
    (net.decomposeWith (fun z => softSplit θ z.1 z.2) x).1 -
      (net.decomposeWith (fun z => softSplit θ z.1 z.2) x).2 = softEval θ net (x.1-x.2))
theorem _ThesisExactChecks.target_91 : _ThesisExpectedTypes.type_91 := by exact @Thesis.SoftplusDecomposition.thesis_softplus_forward
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusDecomposition.thesis_softplus_forward
  let expected ← getConstInfo `_ThesisExactChecks.target_91
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusDecomposition.thesis_softplus_forward"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusDecomposition.thesis_softplus_forward | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusDecomposition do
    throwError "Defining module mismatch: Thesis.SoftplusDecomposition.thesis_softplus_forward"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_91) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusDecomposition.thesis_softplus_forward: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusDecomposition.thesis_softplus_forward"
#check @Thesis.SoftplusDecomposition.thesis_softplus_forward
#print axioms _ThesisExactChecks.target_91

section
open Thesis.Regularization
def _ThesisExpectedTypes.type_92 : Prop := (∀ (θ z : ℝ) (hθ : 0 < θ),
    IsGreatest ((fun p : ℝ => p * z + θ * Real.binEntropy p) '' Set.Icc 0 1)
      (softplus θ z))
theorem _ThesisExactChecks.target_92 : _ThesisExpectedTypes.type_92 := by exact @Thesis.Regularization.softplus_variational
end
run_cmd do
  let target ← getConstInfo `Thesis.Regularization.softplus_variational
  let expected ← getConstInfo `_ThesisExactChecks.target_92
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Regularization.softplus_variational"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Regularization.softplus_variational | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Regularization do
    throwError "Defining module mismatch: Thesis.Regularization.softplus_variational"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_92) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Regularization.softplus_variational: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Regularization.softplus_variational"
#check @Thesis.Regularization.softplus_variational
#print axioms _ThesisExactChecks.target_92

section
open Thesis.Regularization
def _ThesisExpectedTypes.type_93 : Prop := (∀ (θ z p : ℝ) (hθ : 0 < θ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1),
    p * z + θ * Real.binEntropy p = softplus θ z ↔ p = gate θ z)
theorem _ThesisExactChecks.target_93 : _ThesisExpectedTypes.type_93 := by exact @Thesis.Regularization.entropy_gate_unique
end
run_cmd do
  let target ← getConstInfo `Thesis.Regularization.entropy_gate_unique
  let expected ← getConstInfo `_ThesisExactChecks.target_93
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Regularization.entropy_gate_unique"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Regularization.entropy_gate_unique | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Regularization do
    throwError "Defining module mismatch: Thesis.Regularization.entropy_gate_unique"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_93) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Regularization.entropy_gate_unique: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Regularization.entropy_gate_unique"
#check @Thesis.Regularization.entropy_gate_unique
#print axioms _ThesisExactChecks.target_93

section
universe u
open Thesis.Regularization
def _ThesisExpectedTypes.type_94 : Prop := (∀ {A : Type u} [Fintype A] [Nonempty A] (θ : ℝ) (q : A → ℝ) (hθ : 0 < θ),
    IsGreatest ((fun p : A → ℝ => (∑ i, p i * q i) + θ * entropy p) ''
      {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}) (logPartition θ q))
theorem _ThesisExactChecks.target_94 : _ThesisExpectedTypes.type_94.{u} := by exact @Thesis.Regularization.routing_variational.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Regularization.routing_variational
  let expected ← getConstInfo `_ThesisExactChecks.target_94
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Regularization.routing_variational"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Regularization.routing_variational | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Regularization do
    throwError "Defining module mismatch: Thesis.Regularization.routing_variational"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_94) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Regularization.routing_variational: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Regularization.routing_variational"
#check @Thesis.Regularization.routing_variational
#print axioms _ThesisExactChecks.target_94

section
universe u
open Finset Thesis.Regularization Thesis.ReferencePolicy
def _ThesisExpectedTypes.type_95 : Prop := (∀ {A : Type u} [Fintype A] [Nonempty A] (θ : ℝ) (ρ q : A → ℝ) (hθ : 0 < θ)
    (hρ : ∀ i, 0 < ρ i),
    IsGreatest ((fun p : A → ℝ => (∑ i, p i * q i) - θ * kl p ρ) ''
      {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}) (referenceValue θ ρ q))
theorem _ThesisExactChecks.target_95 : _ThesisExpectedTypes.type_95.{u} := by exact @Thesis.ReferencePolicy.thesis_kl_legendre_fenchel.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.ReferencePolicy.thesis_kl_legendre_fenchel
  let expected ← getConstInfo `_ThesisExactChecks.target_95
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.ReferencePolicy.thesis_kl_legendre_fenchel"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReferencePolicy.thesis_kl_legendre_fenchel | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReferencePolicy do
    throwError "Defining module mismatch: Thesis.ReferencePolicy.thesis_kl_legendre_fenchel"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_95) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ReferencePolicy.thesis_kl_legendre_fenchel: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReferencePolicy.thesis_kl_legendre_fenchel"
#check @Thesis.ReferencePolicy.thesis_kl_legendre_fenchel
#print axioms _ThesisExactChecks.target_95

section
universe u
open Finset Thesis.Regularization Thesis.ReferencePolicy
def _ThesisExpectedTypes.type_96 : Prop := (∀ {A : Type u} [Fintype A] [Nonempty A] (θ : ℝ) (ρ q p : A → ℝ) (hθ : 0 < θ)
    (hρ : ∀ i, 0 < ρ i) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1),
    (∑ i, p i * q i) - θ * kl p ρ = referenceValue θ ρ q ↔ p = referencePolicy θ ρ q)
theorem _ThesisExactChecks.target_96 : _ThesisExpectedTypes.type_96.{u} := by exact @Thesis.ReferencePolicy.reference_policy_unique.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.ReferencePolicy.reference_policy_unique
  let expected ← getConstInfo `_ThesisExactChecks.target_96
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.ReferencePolicy.reference_policy_unique"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReferencePolicy.reference_policy_unique | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReferencePolicy do
    throwError "Defining module mismatch: Thesis.ReferencePolicy.reference_policy_unique"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_96) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ReferencePolicy.reference_policy_unique: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReferencePolicy.reference_policy_unique"
#check @Thesis.ReferencePolicy.reference_policy_unique
#print axioms _ThesisExactChecks.target_96

section
universe u
open Finset Thesis.Regularization Thesis.ReferencePolicy
def _ThesisExpectedTypes.type_97 : Prop := (∀ {A : Type u} [Fintype A] [Nonempty A] (ρ u : A → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hu : ∀ i, 0 < u i),
    IsGreatest ((fun p : A → ℝ => (∑ i, p i * Real.log (u i)) - kl p ρ) ''
      {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}) (Real.log (∑ i, ρ i * u i)))
theorem _ThesisExactChecks.target_97 : _ThesisExpectedTypes.type_97.{u} := by exact @Thesis.ReferencePolicy.thesis_attention_value_policy.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.ReferencePolicy.thesis_attention_value_policy
  let expected ← getConstInfo `_ThesisExactChecks.target_97
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.ReferencePolicy.thesis_attention_value_policy"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReferencePolicy.thesis_attention_value_policy | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReferencePolicy do
    throwError "Defining module mismatch: Thesis.ReferencePolicy.thesis_attention_value_policy"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_97) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ReferencePolicy.thesis_attention_value_policy: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReferencePolicy.thesis_attention_value_policy"
#check @Thesis.ReferencePolicy.thesis_attention_value_policy
#print axioms _ThesisExactChecks.target_97

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.AttentionBackward
def _ThesisExpectedTypes.type_98 : Prop := (∀ {T K C D : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (x : Vec (K*D)),
    HasFDerivAt (conditionedAttention A Wv bv) (matrixCLM (effectiveWeight A Wv)) x)
theorem _ThesisExactChecks.target_98 : _ThesisExpectedTypes.type_98 := by exact @Thesis.AttentionBackward.conditionedAttention_hasFDerivAt
end
run_cmd do
  let target ← getConstInfo `Thesis.AttentionBackward.conditionedAttention_hasFDerivAt
  let expected ← getConstInfo `_ThesisExactChecks.target_98
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.AttentionBackward.conditionedAttention_hasFDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AttentionBackward.conditionedAttention_hasFDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AttentionBackward do
    throwError "Defining module mismatch: Thesis.AttentionBackward.conditionedAttention_hasFDerivAt"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_98) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AttentionBackward.conditionedAttention_hasFDerivAt: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AttentionBackward.conditionedAttention_hasFDerivAt"
#check @Thesis.AttentionBackward.conditionedAttention_hasFDerivAt
#print axioms _ThesisExactChecks.target_98

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.AttentionBackward
def _ThesisExpectedTypes.type_99 : Prop := (∀ {T K C D m : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (tail : Network (T*C) m)
    (α β ε : ℝ) (_hα : 0 ≤ α) (_hβ : 0 ≤ β) (_hε : 0 < ε)
    (_hA : ∀ t k, 0 ≤ A t k) (_hA1 : ∀ t, ∑ k, A t k = 1)
    (x : Vec (K*D)) (R : Vec m) (i : Fin (K*D)),
    attentionLRP A Wv bv tail α β ε x R i = ∑ j, R j *
      (attentionOccupation A Wv bv tail α β ε x j i false -
       attentionOccupation A Wv bv tail α β ε x j i true))
theorem _ThesisExactChecks.target_99 : _ThesisExpectedTypes.type_99 := by exact @Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_99
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AttentionBackward do
    throwError "Defining module mismatch: Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_99) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery"
#check @Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery
#print axioms _ThesisExactChecks.target_99

section
open Finset Thesis.Games
def _ThesisExpectedTypes.type_100 : Prop := (∀ {S : Type} [Fintype S] (n : ℕ) (A B : ℕ → S → S → ℝ)
    (hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t) (s : S),
    (∑ path : Paths S n, Real.sqrt (pathLaw n A s path * pathLaw n B s path)) =
      backwardDP n (fun i u v => Real.sqrt (A i u v * B i u v)) (fun _ => 1) s)
theorem _ThesisExactChecks.target_100 : _ThesisExpectedTypes.type_100 := by exact @Thesis.Games.trajectory_overlap_eq_DP
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.trajectory_overlap_eq_DP
  let expected ← getConstInfo `_ThesisExactChecks.target_100
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Games.trajectory_overlap_eq_DP"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.trajectory_overlap_eq_DP | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.trajectory_overlap_eq_DP"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_100) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.trajectory_overlap_eq_DP: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.trajectory_overlap_eq_DP"
#check @Thesis.Games.trajectory_overlap_eq_DP
#print axioms _ThesisExactChecks.target_100

section
open Finset Thesis.Games
def _ThesisExpectedTypes.type_101 : Prop := (∀ {S : Type} [Fintype S] (n : ℕ) (K : ℕ → S → S → ℝ) (h : ℕ → S → ℝ)
    (hh : ∀ i s, h i s ≠ 0) (hterminal : ∀ t, h n t = 1) (s : S) (path : Paths S n),
    pathLaw n (fun i u v => K i u v * h (i+1) v / h i u) s path =
      pathLaw n K s path / h 0 s)
theorem _ThesisExactChecks.target_101 : _ThesisExpectedTypes.type_101 := by exact @Thesis.Games.doob_survival_path
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.doob_survival_path
  let expected ← getConstInfo `_ThesisExactChecks.target_101
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Games.doob_survival_path"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.doob_survival_path | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.doob_survival_path"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_101) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.doob_survival_path: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.doob_survival_path"
#check @Thesis.Games.doob_survival_path
#print axioms _ThesisExactChecks.target_101

section
universe u
open Finset Thesis.Games
def _ThesisExpectedTypes.type_102 : Prop := (∀ {S : Type u} [Fintype S] (p q : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hp1 : ∑ s, p s = 1) (hq1 : ∑ s, q s = 1),
    (1/2 : ℝ) * (∑ s, (Real.sqrt (p s) - Real.sqrt (q s))^2) = 1-overlap p q)
theorem _ThesisExactChecks.target_102 : _ThesisExpectedTypes.type_102.{u} := by exact @Thesis.Games.hellinger_identity.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.hellinger_identity
  let expected ← getConstInfo `_ThesisExactChecks.target_102
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Games.hellinger_identity"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.hellinger_identity | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.hellinger_identity"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_102) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.hellinger_identity: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.hellinger_identity"
#check @Thesis.Games.hellinger_identity
#print axioms _ThesisExactChecks.target_102

section
universe u
open Finset Thesis.Games
def _ThesisExpectedTypes.type_103 : Prop := (∀ {S : Type u} [Fintype S] (p q : S → ℝ) (ZA ZB : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (_hZA : 0 < ZA) (_hZB : 0 < ZB),
    overlap (fun s => p s / ZA) (fun s => q s / ZB) = overlap p q / Real.sqrt (ZA*ZB))
theorem _ThesisExactChecks.target_103 : _ThesisExpectedTypes.type_103.{u} := by exact @Thesis.Games.survival_overlap.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.survival_overlap
  let expected ← getConstInfo `_ThesisExactChecks.target_103
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Games.survival_overlap"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.survival_overlap | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.survival_overlap"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_103) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.survival_overlap: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.survival_overlap"
#check @Thesis.Games.survival_overlap
#print axioms _ThesisExactChecks.target_103

section
universe u
open Finset Thesis.Games
def _ThesisExpectedTypes.type_104 : Prop := (∀ {S : Type u} [Fintype S] (p q : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hp1 : ∑ s, p s = 1) (hq1 : ∑ s, q s = 1),
    overlap p q = 1 ↔ p = q)
theorem _ThesisExactChecks.target_104 : _ThesisExpectedTypes.type_104.{u} := by exact @Thesis.Games.overlap_eq_one_iff.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.overlap_eq_one_iff
  let expected ← getConstInfo `_ThesisExactChecks.target_104
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Games.overlap_eq_one_iff"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.overlap_eq_one_iff | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.overlap_eq_one_iff"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_104) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.overlap_eq_one_iff: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.overlap_eq_one_iff"
#check @Thesis.Games.overlap_eq_one_iff
#print axioms _ThesisExactChecks.target_104

section
universe u
open Finset Thesis.Games
def _ThesisExpectedTypes.type_105 : Prop := (∀ {S : Type u} [Fintype S] (p q : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s),
    overlap p q = 0 ↔ ∀ s, p s = 0 ∨ q s = 0)
theorem _ThesisExactChecks.target_105 : _ThesisExpectedTypes.type_105.{u} := by exact @Thesis.Games.overlap_eq_zero_iff.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.overlap_eq_zero_iff
  let expected ← getConstInfo `_ThesisExactChecks.target_105
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Games.overlap_eq_zero_iff"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.overlap_eq_zero_iff | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.overlap_eq_zero_iff"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_105) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.overlap_eq_zero_iff: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.overlap_eq_zero_iff"
#check @Thesis.Games.overlap_eq_zero_iff
#print axioms _ThesisExactChecks.target_105

section
universe u v
open Finset Thesis.Games Thesis.Coarsening
def _ThesisExpectedTypes.type_106 : Prop := (∀ {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] [DecidableEq Y] (f : X → Y) (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x),
    1 - overlap (pushforward f p) (pushforward f q) ≤ 1 - overlap p q)
theorem _ThesisExactChecks.target_106 : _ThesisExpectedTypes.type_106.{u, v} := by exact @Thesis.Coarsening.hellinger_coarsening.{u, v}
end
run_cmd do
  let target ← getConstInfo `Thesis.Coarsening.hellinger_coarsening
  let expected ← getConstInfo `_ThesisExactChecks.target_106
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: Thesis.Coarsening.hellinger_coarsening"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Coarsening.hellinger_coarsening | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Coarsening do
    throwError "Defining module mismatch: Thesis.Coarsening.hellinger_coarsening"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_106) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Coarsening.hellinger_coarsening: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Coarsening.hellinger_coarsening"
#check @Thesis.Coarsening.hellinger_coarsening
#print axioms _ThesisExactChecks.target_106

section
universe u v
open Finset Thesis.Games Thesis.Coarsening
def _ThesisExpectedTypes.type_107 : Prop := (∀ {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] (erase : X → Y) (recover : Y → X)
    (hleft : Function.LeftInverse recover erase) (hright : Function.RightInverse recover erase)
    (p q : X → ℝ),
    overlap (fun y => p (recover y)) (fun y => q (recover y)) = overlap p q)
theorem _ThesisExactChecks.target_107 : _ThesisExpectedTypes.type_107.{u, v} := by exact @Thesis.Coarsening.surviving_overlap_recovery.{u, v}
end
run_cmd do
  let target ← getConstInfo `Thesis.Coarsening.surviving_overlap_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_107
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: Thesis.Coarsening.surviving_overlap_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Coarsening.surviving_overlap_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Coarsening do
    throwError "Defining module mismatch: Thesis.Coarsening.surviving_overlap_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_107) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Coarsening.surviving_overlap_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Coarsening.surviving_overlap_recovery"
#check @Thesis.Coarsening.surviving_overlap_recovery
#print axioms _ThesisExactChecks.target_107

section
open Finset Thesis.Games Thesis.Randomization
def _ThesisExpectedTypes.type_108 : Prop := (∀ {S : Type} [Fintype S] (A B : Option S → ℝ)
    (hB : ∀ s, 0 ≤ B s) (hBsum : ∑ s, B s = 1) (hBdead : B none = 1),
    (∑ s, Real.sqrt (A (some s) * B (some s))) = 0)
theorem _ThesisExactChecks.target_108 : _ThesisExpectedTypes.type_108 := by exact @Thesis.Randomization.thesis_alive_mismatch_ordinary
end
run_cmd do
  let target ← getConstInfo `Thesis.Randomization.thesis_alive_mismatch_ordinary
  let expected ← getConstInfo `_ThesisExactChecks.target_108
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Randomization.thesis_alive_mismatch_ordinary"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Randomization.thesis_alive_mismatch_ordinary | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Randomization do
    throwError "Defining module mismatch: Thesis.Randomization.thesis_alive_mismatch_ordinary"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_108) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Randomization.thesis_alive_mismatch_ordinary: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Randomization.thesis_alive_mismatch_ordinary"
#check @Thesis.Randomization.thesis_alive_mismatch_ordinary
#print axioms _ThesisExactChecks.target_108

section
open Finset Thesis.Games Thesis.Randomization
def _ThesisExpectedTypes.type_109 : Prop := (∀ {S : Type} [Fintype S] (A B : Option S → ℝ)
    (hAstop : A none = 0) (hB : ∀ s, 0 ≤ B s) (hBsum : ∑ s, B s = 1) (hBdead : B none = 1),
    (∑ s, Real.sqrt (A s * B s)) = 0)
theorem _ThesisExactChecks.target_109 : _ThesisExpectedTypes.type_109 := by exact @Thesis.Randomization.thesis_alive_mismatch_full
end
run_cmd do
  let target ← getConstInfo `Thesis.Randomization.thesis_alive_mismatch_full
  let expected ← getConstInfo `_ThesisExactChecks.target_109
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Randomization.thesis_alive_mismatch_full"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Randomization.thesis_alive_mismatch_full | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Randomization do
    throwError "Defining module mismatch: Thesis.Randomization.thesis_alive_mismatch_full"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_109) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Randomization.thesis_alive_mismatch_full: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Randomization.thesis_alive_mismatch_full"
#check @Thesis.Randomization.thesis_alive_mismatch_full
#print axioms _ThesisExactChecks.target_109

section
open Finset Thesis.Games Thesis.Randomization
def _ThesisExpectedTypes.type_110 : Prop := (∀ {S : Type} [Fintype S] (n extra : ℕ) (A B : ℕ → S → S → ℝ)
    (aliveA aliveB : ℕ → S → Bool) (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1)
    (hA : ∀ l s t, 0 ≤ A l s t) (hB : ∀ l s t, 0 ≤ B l s t)
    (hArow : ∀ l s, ∑ t, A l s t ≤ 1) (hBrow : ∀ l s, ∑ t, B l s t ≤ 1)
    (hdeadA : ∀ l s, aliveA l s = false → ∀ t, A l s t = 0)
    (hdeadB : ∀ l s, aliveB l s = false → ∀ t, B l s t = 0)
    (hrow : ∀ l < n, ∀ s, aliveA l s = true ∧ aliveB l s = true →
      (∑ t, Real.sqrt (A l s t * B l s t)) ≤ b) (s : S),
    ordinaryOverlap (n+extra) A B s ≤ b^n)
theorem _ThesisExactChecks.target_110 : _ThesisExpectedTypes.type_110 := by exact @Thesis.Randomization.thesis_randomization_routing_full_depth
end
run_cmd do
  let target ← getConstInfo `Thesis.Randomization.thesis_randomization_routing_full_depth
  let expected ← getConstInfo `_ThesisExactChecks.target_110
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Randomization.thesis_randomization_routing_full_depth"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Randomization.thesis_randomization_routing_full_depth | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Randomization do
    throwError "Defining module mismatch: Thesis.Randomization.thesis_randomization_routing_full_depth"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_110) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Randomization.thesis_randomization_routing_full_depth: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Randomization.thesis_randomization_routing_full_depth"
#check @Thesis.Randomization.thesis_randomization_routing_full_depth
#print axioms _ThesisExactChecks.target_110

section
universe u
open MeasureTheory Filter Finset Thesis.Games Thesis.Randomization Thesis.RandomizationExpectation
open scoped MeasureTheory
def _ThesisExpectedTypes.type_111 : Prop := (∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] {S : Type} [Fintype S] [DecidableEq S] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : ℕ → MeasurableSpace Ω) (hm : ∀ n, ℱ n ≤ mΩ)
    (A : ℕ → S → S → ℝ) (B : ℕ → Ω → S → S → ℝ) (alive : ℕ → Ω → S → Bool)
    (s₀ : S) (η : ℝ) (hη : 0 ≤ η)
    (hA : ∀ n s t, 0 ≤ A n s t) (hB : ∀ n ω s t, 0 ≤ B n ω s t)
    (hArow : ∀ n s, ∑ t, A n s t ≤ 1) (hBrow : ∀ n ω s, ∑ t, B n ω s t ≤ 1)
    (hdead : ∀ n ω s, alive n ω s = false → ∀ t, B n ω s t = 0)
    (hg : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (ha : ∀ n s, Integrable (fun ω => if alive n ω s then (1:ℝ) else 0) μ)
    (hga : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s *
      (if alive n ω s then (1:ℝ) else 0)) μ)
    (hgm : ∀ n s, AEStronglyMeasurable[ℱ n] (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (n extra : ℕ) (hcond : ∀ l < n, ∀ s, ∀ᵐ ω ∂μ,
      μ[(fun ω => if alive l ω s then (1:ℝ) else 0) | ℱ l] ω ≤ η),
    (∫ ω, ordinaryOverlap (n+extra) A (fun l => B l ω) s₀ ∂μ) ≤ η^n)
theorem _ThesisExactChecks.target_111 : _ThesisExpectedTypes.type_111.{u} := by exact @Thesis.RandomizationExpectation.thesis_rand_adf_full_depth.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RandomizationExpectation.thesis_rand_adf_full_depth
  let expected ← getConstInfo `_ThesisExactChecks.target_111
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RandomizationExpectation.thesis_rand_adf_full_depth"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RandomizationExpectation.thesis_rand_adf_full_depth | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RandomizationExpectation do
    throwError "Defining module mismatch: Thesis.RandomizationExpectation.thesis_rand_adf_full_depth"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_111) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RandomizationExpectation.thesis_rand_adf_full_depth: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RandomizationExpectation.thesis_rand_adf_full_depth"
#check @Thesis.RandomizationExpectation.thesis_rand_adf_full_depth
#print axioms _ThesisExactChecks.target_111

section
universe u
open MeasureTheory Filter Finset Thesis.Games Thesis.Randomization Thesis.RandomizationExpectation
open scoped MeasureTheory
def _ThesisExpectedTypes.type_112 : Prop := (∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c Z : Ω → ℝ) (z C : ℝ) (hz : 0 < z)
    (hc0 : ∀ᵐ ω ∂μ, 0 ≤ c ω) (hc : Integrable c μ)
    (hE : MeasurableSet {ω | z ≤ Z ω})
    (hH : Integrable (fun ω => if z ≤ Z ω then 1 - c ω / Real.sqrt (Z ω) else 0) μ)
    (hbound : (∫ ω, c ω ∂μ) ≤ C),
    μ.real {ω | z ≤ Z ω} - C / Real.sqrt z ≤
      ∫ ω, (if z ≤ Z ω then 1 - c ω / Real.sqrt (Z ω) else 0) ∂μ)
theorem _ThesisExactChecks.target_112 : _ThesisExpectedTypes.type_112.{u} := by exact @Thesis.RandomizationExpectation.thesis_conditioned_survival_lower.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RandomizationExpectation.thesis_conditioned_survival_lower
  let expected ← getConstInfo `_ThesisExactChecks.target_112
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RandomizationExpectation.thesis_conditioned_survival_lower"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RandomizationExpectation.thesis_conditioned_survival_lower | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RandomizationExpectation do
    throwError "Defining module mismatch: Thesis.RandomizationExpectation.thesis_conditioned_survival_lower"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_112) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RandomizationExpectation.thesis_conditioned_survival_lower: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RandomizationExpectation.thesis_conditioned_survival_lower"
#check @Thesis.RandomizationExpectation.thesis_conditioned_survival_lower
#print axioms _ThesisExactChecks.target_112

section
universe u v
open Finset Thesis.Games Thesis.Coarsening
def _ThesisExpectedTypes.type_113 : Prop := (∀ {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] [DecidableEq Y] (f : X → Y) (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x),
    overlap p q ≤ overlap (pushforward f p) (pushforward f q))
theorem _ThesisExactChecks.target_113 : _ThesisExpectedTypes.type_113.{u, v} := by exact @Thesis.Coarsening.overlap_coarsening.{u, v}
end
run_cmd do
  let target ← getConstInfo `Thesis.Coarsening.overlap_coarsening
  let expected ← getConstInfo `_ThesisExactChecks.target_113
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: Thesis.Coarsening.overlap_coarsening"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Coarsening.overlap_coarsening | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Coarsening do
    throwError "Defining module mismatch: Thesis.Coarsening.overlap_coarsening"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_113) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Coarsening.overlap_coarsening: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Coarsening.overlap_coarsening"
#check @Thesis.Coarsening.overlap_coarsening
#print axioms _ThesisExactChecks.target_113

section
universe u v
open Finset Thesis.Games
def _ThesisExpectedTypes.type_114 : Prop := (∀ {S : Type u} {T : Type v} [Fintype S] [Fintype T] (A B : S → T → ℝ)
    (hA : ∀ s t, 0 ≤ A s t) (hB : ∀ s t, 0 ≤ B s t)
    (hA1 : ∀ s, ∑ t, A s t = 1) (hB1 : ∀ s, ∑ t, B s t = 1) (s : S),
    (∑ t, Real.sqrt (A s t * B s t)) ≤ 1)
theorem _ThesisExactChecks.target_114 : _ThesisExpectedTypes.type_114.{u, v} := by exact @Thesis.Games.geometric_kernel_substochastic.{u, v}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.geometric_kernel_substochastic
  let expected ← getConstInfo `_ThesisExactChecks.target_114
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: Thesis.Games.geometric_kernel_substochastic"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.geometric_kernel_substochastic | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.geometric_kernel_substochastic"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_114) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.geometric_kernel_substochastic: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.geometric_kernel_substochastic"
#check @Thesis.Games.geometric_kernel_substochastic
#print axioms _ThesisExactChecks.target_114

section
open Finset Thesis.Games
def _ThesisExpectedTypes.type_115 : Prop := (∀ {S : Type} [Fintype S] (n : ℕ) (A B : ℕ → S → S → ℝ)
    (hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
    (s : S) (path : Paths S n),
    Real.sqrt (pathLaw n A s path * pathLaw n B s path) =
      pathLaw n (fun i u v => Real.sqrt (A i u v * B i u v)) s path)
theorem _ThesisExactChecks.target_115 : _ThesisExpectedTypes.type_115 := by exact @Thesis.Games.path_geometric_mean
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.path_geometric_mean
  let expected ← getConstInfo `_ThesisExactChecks.target_115
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Games.path_geometric_mean"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.path_geometric_mean | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.path_geometric_mean"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_115) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.path_geometric_mean: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.path_geometric_mean"
#check @Thesis.Games.path_geometric_mean
#print axioms _ThesisExactChecks.target_115

section
universe u v
open Finset Thesis.Games
def _ThesisExpectedTypes.type_116 : Prop := (∀ {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] [DecidableEq Y] (p q : X → ℝ) (terminal : X → Y)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (y : Y),
    0 ≤ pixelDisagreement p q terminal y)
theorem _ThesisExactChecks.target_116 : _ThesisExpectedTypes.type_116.{u, v} := by exact @Thesis.Games.pixelDisagreement_nonneg.{u, v}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.pixelDisagreement_nonneg
  let expected ← getConstInfo `_ThesisExactChecks.target_116
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: Thesis.Games.pixelDisagreement_nonneg"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.pixelDisagreement_nonneg | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.pixelDisagreement_nonneg"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_116) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.pixelDisagreement_nonneg: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.pixelDisagreement_nonneg"
#check @Thesis.Games.pixelDisagreement_nonneg
#print axioms _ThesisExactChecks.target_116

section
open Thesis.Regularization
def _ThesisExpectedTypes.type_117 : Prop := (∀ (θ u v : ℝ) (hθ : 0 < θ),
    (softSplit θ u v).1 - (softSplit θ u v).2 = softplus θ (u - v))
theorem _ThesisExactChecks.target_117 : _ThesisExpectedTypes.type_117 := by exact @Thesis.Regularization.softSplit_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.Regularization.softSplit_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_117
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Regularization.softSplit_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Regularization.softSplit_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Regularization do
    throwError "Defining module mismatch: Thesis.Regularization.softSplit_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_117) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Regularization.softSplit_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Regularization.softSplit_recovery"
#check @Thesis.Regularization.softSplit_recovery
#print axioms _ThesisExactChecks.target_117

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology
def _ThesisExpectedTypes.type_118 : Prop := (∀ (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)),
    Tendsto (deriv f) atBot (𝓝 (minusInfinitySlope f)) ∧
    (∃ B : ℝ, ∀ x, |deriv f x| ≤ B) ∧
    ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
    ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
    Monotone (tilt (C1 f) (commonTilt f)) ∧
    Monotone (tilt (C2 f) (commonTilt f)) ∧
    ∀ z : ℝ × ℝ, tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2))
theorem _ThesisExactChecks.target_118 : _ThesisExpectedTypes.type_118 := by exact @HiddenMonotonicity.SmoothDC.smooth_dc_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.smooth_dc_split
  let expected ← getConstInfo `_ThesisExactChecks.target_118
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.smooth_dc_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.smooth_dc_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SmoothCurvatureSplit do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.smooth_dc_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_118) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.smooth_dc_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.smooth_dc_split"
#check @HiddenMonotonicity.SmoothDC.smooth_dc_split
#print axioms _ThesisExactChecks.target_118

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology
def _ThesisExpectedTypes.type_119 : Prop := (∀ (f : ℝ → ℝ) (hq : Integrable (curvature f)),
    ∀ L, Monotone (tilt (C1 f) L) → Monotone (tilt (C2 f) L) → commonTilt f≤L)
theorem _ThesisExactChecks.target_119 : _ThesisExpectedTypes.type_119 := by exact @HiddenMonotonicity.SmoothDC.canonical_tilt_minimality
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.canonical_tilt_minimality
  let expected ← getConstInfo `_ThesisExactChecks.target_119
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.canonical_tilt_minimality"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.canonical_tilt_minimality | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SmoothCurvatureSplit do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.canonical_tilt_minimality"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_119) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.canonical_tilt_minimality: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.canonical_tilt_minimality"
#check @HiddenMonotonicity.SmoothDC.canonical_tilt_minimality
#print axioms _ThesisExactChecks.target_119

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology
def _ThesisExpectedTypes.type_120 : Prop := (    let f := Real.sigmoid
    ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
    ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
    Monotone (tilt (C1 f) (commonTilt f)) ∧ Monotone (tilt (C2 f) (commonTilt f)) ∧
    ∀ z, tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2))
theorem _ThesisExactChecks.target_120 : _ThesisExpectedTypes.type_120 := by exact @HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split
  let expected ← getConstInfo `_ThesisExactChecks.target_120
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernSigmoid do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_120) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split"
#check @HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split
#print axioms _ThesisExactChecks.target_120

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology
def _ThesisExpectedTypes.type_121 : Prop := (∀ (θ : ℝ) (hθ : 0<θ),
    let f := Thesis.Regularization.softplus θ
    ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
    ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
    Monotone (tilt (C1 f) (commonTilt f)) ∧ Monotone (tilt (C2 f) (commonTilt f)) ∧
    ∀ z, tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2))
theorem _ThesisExactChecks.target_121 : _ThesisExpectedTypes.type_121 := by exact @HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split
  let expected ← getConstInfo `_ThesisExactChecks.target_121
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernSoftplus do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_121) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split"
#check @HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split
#print axioms _ThesisExactChecks.target_121

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology
def _ThesisExpectedTypes.type_122 : Prop := (∀ (f c1 c2 : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hfAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f))
    (hc1 : ConvexOn ℝ univ c1) (hd1 : Differentiable ℝ c1)
    (hAC1 : ∀ a b, AbsolutelyContinuousOnInterval (deriv c1) a b)
    (heq : ∀ x, f x=c1 x-c2 x)
    (hminimal : ∀ᵐ x, curvature c1 x=positiveCurvature f x),
    ∃ a b : ℝ, (∀ x, c1 x=C1 f x+a*x+b) ∧ (∀ x, c2 x=C2 f x+a*x+b))
theorem _ThesisExactChecks.target_122 : _ThesisExpectedTypes.type_122 := by exact @HiddenMonotonicity.SmoothDC.common_affine_of_minimal_curvature
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.common_affine_of_minimal_curvature
  let expected ← getConstInfo `_ThesisExactChecks.target_122
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.common_affine_of_minimal_curvature"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.common_affine_of_minimal_curvature | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.CurvatureMinimality do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.common_affine_of_minimal_curvature"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_122) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.common_affine_of_minimal_curvature: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.common_affine_of_minimal_curvature"
#check @HiddenMonotonicity.SmoothDC.common_affine_of_minimal_curvature
#print axioms _ThesisExactChecks.target_122

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology
def _ThesisExpectedTypes.type_123 : Prop := (∀ (f c1 c2 : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hfAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f))
    (hc1 : ConvexOn ℝ univ c1) (hc2 : ConvexOn ℝ univ c2)
    (hd1 : Differentiable ℝ c1) (hd2 : Differentiable ℝ c2)
    (hAC1 : ∀ a b, AbsolutelyContinuousOnInterval (deriv c1) a b)
    (heq : ∀ x, f x=c1 x-c2 x),
    (∀ᵐ x, positiveCurvature f x≤curvature c1 x ∧ negativeCurvature f x≤curvature c2 x) ∧
    ((∀ᵐ x, curvature c1 x=positiveCurvature f x ∧ curvature c2 x=negativeCurvature f x) →
      ∃ a b : ℝ, (∀ x, c1 x=C1 f x+a*x+b) ∧ (∀ x, c2 x=C2 f x+a*x+b)) ∧
    (∀ L, Monotone (tilt (C1 f) L) → Monotone (tilt (C2 f) L) → commonTilt f≤L))
theorem _ThesisExactChecks.target_123 : _ThesisExpectedTypes.type_123 := by exact @HiddenMonotonicity.SmoothDC.curvature_minimality_locally_AC
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.curvature_minimality_locally_AC
  let expected ← getConstInfo `_ThesisExactChecks.target_123
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.curvature_minimality_locally_AC"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.curvature_minimality_locally_AC | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.CurvatureMinimality do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.curvature_minimality_locally_AC"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_123) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.curvature_minimality_locally_AC: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.curvature_minimality_locally_AC"
#check @HiddenMonotonicity.SmoothDC.curvature_minimality_locally_AC
#print axioms _ThesisExactChecks.target_123

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology
def _ThesisExpectedTypes.type_124 : Prop := (∀ x : ℝ, curvature Real.tanh x=-2*Real.tanh x/(Real.cosh x)^2)
theorem _ThesisExactChecks.target_124 : _ThesisExpectedTypes.type_124 := by exact @HiddenMonotonicity.SmoothDC.tanh_curvature_sech
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.tanh_curvature_sech
  let expected ← getConstInfo `_ThesisExactChecks.target_124
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.tanh_curvature_sech"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.tanh_curvature_sech | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernTanh do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.tanh_curvature_sech"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_124) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.tanh_curvature_sech: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.tanh_curvature_sech"
#check @HiddenMonotonicity.SmoothDC.tanh_curvature_sech
#print axioms _ThesisExactChecks.target_124

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology
def _ThesisExpectedTypes.type_125 : Prop := (∀ x : ℝ, (0≤x → positiveCurvature Real.tanh x=0) ∧
    (x≤0 → negativeCurvature Real.tanh x=0))
theorem _ThesisExactChecks.target_125 : _ThesisExpectedTypes.type_125 := by exact @HiddenMonotonicity.SmoothDC.tanh_curvature_support
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.tanh_curvature_support
  let expected ← getConstInfo `_ThesisExactChecks.target_125
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.tanh_curvature_support"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.tanh_curvature_support | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernTanh do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.tanh_curvature_support"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_125) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.tanh_curvature_support: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.tanh_curvature_support"
#check @HiddenMonotonicity.SmoothDC.tanh_curvature_support
#print axioms _ThesisExactChecks.target_125

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology
def _ThesisExpectedTypes.type_126 : Prop := (Integrable (curvature Real.tanh) ∧
    (∀ a b, AbsolutelyContinuousOnInterval (deriv Real.tanh) a b) ∧
    ConvexOn ℝ univ (tilt (C1 Real.tanh) (commonTilt Real.tanh)) ∧
    ConvexOn ℝ univ (tilt (C2 Real.tanh) (commonTilt Real.tanh)) ∧
    Monotone (tilt (C1 Real.tanh) (commonTilt Real.tanh)) ∧
    Monotone (tilt (C2 Real.tanh) (commonTilt Real.tanh)) ∧
    ValidPairActivation Real.tanh (splitPair Real.tanh) ∧
    NonnegativePairActivation (splitPair Real.tanh))
theorem _ThesisExactChecks.target_126 : _ThesisExpectedTypes.type_126 := by exact @HiddenMonotonicity.SmoothDC.tanh_smooth_dc_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.tanh_smooth_dc_split
  let expected ← getConstInfo `_ThesisExactChecks.target_126
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.tanh_smooth_dc_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.tanh_smooth_dc_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernTanh do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.tanh_smooth_dc_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_126) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.tanh_smooth_dc_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.tanh_smooth_dc_split"
#check @HiddenMonotonicity.SmoothDC.tanh_smooth_dc_split
#print axioms _ThesisExactChecks.target_126

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology
def _ThesisExpectedTypes.type_127 : Prop := (∀ (θ : ℝ) (hθ : 0<θ),
    negativeCurvature (Thesis.Regularization.softplus θ)=0 ∧
    C2 (Thesis.Regularization.softplus θ)=0 ∧
    C1 (Thesis.Regularization.softplus θ)=Thesis.Regularization.softplus θ ∧
    ConvexOn ℝ univ (Thesis.Regularization.softplus θ) ∧
    NonnegativePairActivation (splitPair (Thesis.Regularization.softplus θ)))
theorem _ThesisExactChecks.target_127 : _ThesisExpectedTypes.type_127 := by exact @HiddenMonotonicity.SmoothDC.softplus_degenerate_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.softplus_degenerate_split
  let expected ← getConstInfo `_ThesisExactChecks.target_127
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.softplus_degenerate_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.softplus_degenerate_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernSoftplus do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.softplus_degenerate_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_127) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.softplus_degenerate_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.softplus_degenerate_split"
#check @HiddenMonotonicity.SmoothDC.softplus_degenerate_split
#print axioms _ThesisExactChecks.target_127

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_128 : Prop := (∀ (w : ℝ), max w 0 - max (-w) 0 = w ∧ max w 0 + max (-w) 0 = |w|)
theorem _ThesisExactChecks.target_128 : _ThesisExpectedTypes.type_128 := by exact @HiddenMonotonicity.canonical_weight_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.canonical_weight_split
  let expected ← getConstInfo `_ThesisExactChecks.target_128
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.canonical_weight_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.canonical_weight_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Sensitivities do
    throwError "Defining module mismatch: HiddenMonotonicity.canonical_weight_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_128) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.canonical_weight_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.canonical_weight_split"
#check @HiddenMonotonicity.canonical_weight_split
#print axioms _ThesisExactChecks.target_128

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_129 : Prop := (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (x : PairVec n) (r : Row m) (head : Bool),
 ((net.trace x).stabilized (fun _ => 0) r head).1 + ((net.trace x).stabilized (fun _ => 0) r head).2 = r.comp net.absoluteMap)
theorem _ThesisExactChecks.target_129 : _ThesisExpectedTypes.type_129 := by exact @HiddenMonotonicity.Network.sensitivity_complementarity_absolute
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.sensitivity_complementarity_absolute
  let expected ← getConstInfo `_ThesisExactChecks.target_129
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.sensitivity_complementarity_absolute"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.sensitivity_complementarity_absolute | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.OriginalTrace do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.sensitivity_complementarity_absolute"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_129) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.sensitivity_complementarity_absolute: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.sensitivity_complementarity_absolute"
#check @HiddenMonotonicity.Network.sensitivity_complementarity_absolute
#print axioms _ThesisExactChecks.target_129

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_130 : Prop := (∀ {n m : ℕ} (net : Network n m) (x : Vec n) (hx : net.Strict x) (r : Row m) (head : Bool),
 HasFDerivAt (fun y : Vec n => if head then r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).1 else r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).2)
 (unified ((net.originalTrace x).stabilized (fun _ => 0) r head)) x)
theorem _ThesisExactChecks.target_130 : _ThesisExpectedTypes.type_130 := by exact @HiddenMonotonicity.Network.symmetric_head_derivative
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.symmetric_head_derivative
  let expected ← getConstInfo `_ThesisExactChecks.target_130
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.symmetric_head_derivative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.symmetric_head_derivative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.QSources do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.symmetric_head_derivative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_130) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.symmetric_head_derivative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.symmetric_head_derivative"
#check @HiddenMonotonicity.Network.symmetric_head_derivative
#print axioms _ThesisExactChecks.target_130

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_131 : Prop := (∀ {n m : ℕ} (tr : MaskedTrace n m) (α : ℕ → ℝ) (r : Row m) (head : Bool),
 (tr.stabilized α r head).1 + (tr.stabilized α r head).2 = tr.bulkCoefficient α • (r.comp tr.absMap))
theorem _ThesisExactChecks.target_131 : _ThesisExpectedTypes.type_131 := by exact @HiddenMonotonicity.MaskedTrace.stabilized_bulk
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaskedTrace.stabilized_bulk
  let expected ← getConstInfo `_ThesisExactChecks.target_131
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaskedTrace.stabilized_bulk"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaskedTrace.stabilized_bulk | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.StabilizedBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.MaskedTrace.stabilized_bulk"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_131) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaskedTrace.stabilized_bulk: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaskedTrace.stabilized_bulk"
#check @HiddenMonotonicity.MaskedTrace.stabilized_bulk
#print axioms _ThesisExactChecks.target_131

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_132 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (x : PairVec n) (v : Vec n) (D : PairVec k →L[ℝ] ℝ),
 (D.comp (layerJac wp wn bp bn x)) (v,0) = D (blockPP wp wn bp bn x v,0) + D (0,matrixCLM wn v))
theorem _ThesisExactChecks.target_132 : _ThesisExpectedTypes.type_132 := by exact @HiddenMonotonicity.actual_positive_pullback
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.actual_positive_pullback
  let expected ← getConstInfo `_ThesisExactChecks.target_132
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.actual_positive_pullback"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.actual_positive_pullback | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.NetworkDerivative do
    throwError "Defining module mismatch: HiddenMonotonicity.actual_positive_pullback"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_132) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.actual_positive_pullback: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.actual_positive_pullback"
#check @HiddenMonotonicity.actual_positive_pullback
#print axioms _ThesisExactChecks.target_132

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_133 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (x : PairVec n) (v : Vec n) (D : PairVec k →L[ℝ] ℝ),
 (D.comp (layerJac wp wn bp bn x)) (0,v) = D (blockPN wp wn bp bn x v,0) + D (0,matrixCLM wp v))
theorem _ThesisExactChecks.target_133 : _ThesisExpectedTypes.type_133 := by exact @HiddenMonotonicity.actual_negative_pullback
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.actual_negative_pullback
  let expected ← getConstInfo `_ThesisExactChecks.target_133
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.actual_negative_pullback"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.actual_negative_pullback | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.NetworkDerivative do
    throwError "Defining module mismatch: HiddenMonotonicity.actual_negative_pullback"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_133) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.actual_negative_pullback: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.actual_negative_pullback"
#check @HiddenMonotonicity.actual_negative_pullback
#print axioms _ThesisExactChecks.target_133

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_134 := (∀ {n m : ℕ}, MaskedTrace n m → (ℕ → ℝ) → Row m → Bool → Sensitivity n)
noncomputable def _ThesisExactChecks.target_134 : _ThesisExpectedTypes.type_134 := by exact @HiddenMonotonicity.MaskedTrace.stabilized
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaskedTrace.stabilized
  let expected ← getConstInfo `_ThesisExactChecks.target_134
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaskedTrace.stabilized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaskedTrace.stabilized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.StabilizedBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.MaskedTrace.stabilized"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_134) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaskedTrace.stabilized: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaskedTrace.stabilized"
#check @HiddenMonotonicity.MaskedTrace.stabilized
#print axioms _ThesisExactChecks.target_134

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_135 : Prop := (∀ {n m : ℕ} (net : Network n m) (p q c : Fin n → ℝ),
 net.split (p+c) (q+c) = ((net.split p q).1 + net.common c, (net.split p q).2 + net.common c))
theorem _ThesisExactChecks.target_135 : _ThesisExpectedTypes.type_135 := by exact @HiddenMonotonicity.Network.shift
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.shift
  let expected ← getConstInfo `_ThesisExactChecks.target_135
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.shift"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.shift | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Network do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.shift"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_135) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.shift: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.shift"
#check @HiddenMonotonicity.Network.shift
#print axioms _ThesisExactChecks.target_135

section
universe u
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_136 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] [DecidableEq ι] (p n : ι → ℝ),
 Finset.univ.sup' Finset.univ_nonempty (fun j => p j + ∑ i ∈ Finset.univ.erase j, n i) - ∑ i, n i = Finset.univ.sup' Finset.univ_nonempty (fun j => p j-n j))
theorem _ThesisExactChecks.target_136 : _ThesisExpectedTypes.type_136.{u} := by exact @HiddenMonotonicity.maxpool_correct.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.maxpool_correct
  let expected ← getConstInfo `_ThesisExactChecks.target_136
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.maxpool_correct"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.maxpool_correct | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Chunks do
    throwError "Defining module mismatch: HiddenMonotonicity.maxpool_correct"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_136) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.maxpool_correct: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.maxpool_correct"
#check @HiddenMonotonicity.maxpool_correct
#print axioms _ThesisExactChecks.target_136

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_137 : Prop := (∀ {n : ℕ} (g : (Fin n → ℝ) → ℝ) (x v : Fin n → ℝ) (D : (Fin n → ℝ) →L[ℝ] ℝ)
 (hg : Monotone g) (hd : HasFDerivAt g D x) (hv : 0≤v), 0≤D v)
theorem _ThesisExactChecks.target_137 : _ThesisExpectedTypes.type_137 := by exact @HiddenMonotonicity.monotone_directional_nonnegative
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.monotone_directional_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_137
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.monotone_directional_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.monotone_directional_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Sensitivities do
    throwError "Defining module mismatch: HiddenMonotonicity.monotone_directional_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_137) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.monotone_directional_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.monotone_directional_nonnegative"
#check @HiddenMonotonicity.monotone_directional_nonnegative
#print axioms _ThesisExactChecks.target_137

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_138 : Prop := (∀ {n m : ℕ} (net : Network n m) (σ : ℝ → ℝ) (φ : (ℝ × ℝ) → ℝ × ℝ)
 (hv : ValidPairActivation σ φ) (x : PairVec n),
 (net.decomposeWith φ x).1-(net.decomposeWith φ x).2 = net.forwardWith σ (x.1-x.2))
theorem _ThesisExactChecks.target_138 : _ThesisExpectedTypes.type_138 := by exact @HiddenMonotonicity.Network.valid_decomposition_recovery
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.valid_decomposition_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_138
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.valid_decomposition_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.valid_decomposition_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Decomposition do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.valid_decomposition_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_138) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.valid_decomposition_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.valid_decomposition_recovery"
#check @HiddenMonotonicity.Network.valid_decomposition_recovery
#print axioms _ThesisExactChecks.target_138

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_139 : Prop := (∀ {n m : ℕ} (net : Network n m) (η : ℝ) (x : PairVec n),
 (net.decomposeWith (mixPair η) x).1-(net.decomposeWith (mixPair η) x).2 = net.eval (x.1-x.2))
theorem _ThesisExactChecks.target_139 : _ThesisExpectedTypes.type_139 := by exact @HiddenMonotonicity.Network.mixing_recovery
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.mixing_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_139
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.mixing_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.mixing_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Decomposition do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.mixing_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_139) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.mixing_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.mixing_recovery"
#check @HiddenMonotonicity.Network.mixing_recovery
#print axioms _ThesisExactChecks.target_139

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_140 : Prop := (∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative)
 (p q p' q' : Fin n → ℝ) (t : ℝ) (ht : 0≤t) (ht' : t≤1),
 (net.split (mix t p p') (mix t q q')).1 ≤ mix t (net.split p q).1 (net.split p' q').1 ∧
 (net.split (mix t p p') (mix t q q')).2 ≤ mix t (net.split p q).2 (net.split p' q').2)
theorem _ThesisExactChecks.target_140 : _ThesisExpectedTypes.type_140 := by exact @HiddenMonotonicity.Network.convex
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.convex
  let expected ← getConstInfo `_ThesisExactChecks.target_140
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.convex"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.convex | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Convexity do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.convex"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_140) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.convex: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.convex"
#check @HiddenMonotonicity.Network.convex
#print axioms _ThesisExactChecks.target_140

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_141 : Prop := (∀ {n m : ℕ} (net : Network n m) (x : PairVec n), net.decomposeWith (mixPair 1) x = net.split x.1 x.2)
theorem _ThesisExactChecks.target_141 : _ThesisExpectedTypes.type_141 := by exact @HiddenMonotonicity.Network.mixing_one_is_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.mixing_one_is_split
  let expected ← getConstInfo `_ThesisExactChecks.target_141
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.mixing_one_is_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.mixing_one_is_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Decomposition do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.mixing_one_is_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_141) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.mixing_one_is_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.mixing_one_is_split"
#check @HiddenMonotonicity.Network.mixing_one_is_split
#print axioms _ThesisExactChecks.target_141

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_142 : Prop := (∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative)
 (p q p' q' : Fin n → ℝ) (hp : p≤p') (hq : q≤q'),
 (net.split p q).1 ≤ (net.split p' q').1 ∧ (net.split p q).2 ≤ (net.split p' q').2)
theorem _ThesisExactChecks.target_142 : _ThesisExpectedTypes.type_142 := by exact @HiddenMonotonicity.Network.monotone
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.monotone
  let expected ← getConstInfo `_ThesisExactChecks.target_142
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.monotone"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.monotone | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Convexity do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.monotone"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_142) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.monotone: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.monotone"
#check @HiddenMonotonicity.Network.monotone
#print axioms _ThesisExactChecks.target_142

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_143 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Fin k → ℝ) (p q : Fin n → ℝ),
 (fun i => max ((wp.mulVec p + wn.mulVec q + bp) i) ((wn.mulVec p + wp.mulVec q + bn) i)) -
 (wn.mulVec p + wp.mulVec q + bn) = (fun i => relu (((wp-wn).mulVec (p-q) + (bp-bn)) i)))
theorem _ThesisExactChecks.target_143 : _ThesisExpectedTypes.type_143 := by exact @HiddenMonotonicity.layer_difference
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.layer_difference
  let expected ← getConstInfo `_ThesisExactChecks.target_143
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.layer_difference"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.layer_difference | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Network do
    throwError "Defining module mismatch: HiddenMonotonicity.layer_difference"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_143) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.layer_difference: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.layer_difference"
#check @HiddenMonotonicity.layer_difference
#print axioms _ThesisExactChecks.target_143

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_144 : Prop := (∀ {n m : ℕ} (net : Network n m) (x : Vec n) (hx : net.Strict x) (j : Fin m) (i : Fin n)
 (hblocked : ∀ path : Thesis.BackwardGames.Paths (net.originalTrace x),
 PathConnected (net.originalTrace x) j i path → PathHasInactive (net.originalTrace x) path),
 ∃ U : Set (Vec n), IsOpen U ∧ x∈U ∧ ∀ y∈U, fderiv ℝ net.eval y (Pi.single i 1) j=0)
theorem _ThesisExactChecks.target_144 : _ThesisExpectedTypes.type_144 := by exact @HiddenMonotonicity.Network.gradient_blindness
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.gradient_blindness
  let expected ← getConstInfo `_ThesisExactChecks.target_144
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.gradient_blindness"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.gradient_blindness | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.BlockedPaths do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.gradient_blindness"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_144) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.gradient_blindness: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.gradient_blindness"
#check @HiddenMonotonicity.Network.gradient_blindness
#print axioms _ThesisExactChecks.target_144

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_145 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (x : PairVec n)
 (hx : ∀ i, (preP wp wn x+bp) i ≠ (preN wp wn x+bn) i),
 HasFDerivAt (layerFun wp wn bp bn) (layerJac wp wn bp bn x) x)
theorem _ThesisExactChecks.target_145 : _ThesisExpectedTypes.type_145 := by exact @HiddenMonotonicity.layer_derivative
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.layer_derivative
  let expected ← getConstInfo `_ThesisExactChecks.target_145
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.layer_derivative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.layer_derivative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.NetworkDerivative do
    throwError "Defining module mismatch: HiddenMonotonicity.layer_derivative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_145) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.layer_derivative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.layer_derivative"
#check @HiddenMonotonicity.layer_derivative
#print axioms _ThesisExactChecks.target_145

section
universe u
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_146 : Prop := (∀ {ι : Type u} (e : MaxPolynomial ι), ∃ ps : List (MvPolynomial ι ℝ), ps≠[] ∧
 (∀ p∈ps, ∀ d : ι →₀ ℕ, 0≤p.coeff d) ∧
 ∀ x : ι → ℝ, 0≤x → e.eval x=foldMax (ps.map (MvPolynomial.eval x)))
theorem _ThesisExactChecks.target_146 : _ThesisExpectedTypes.type_146.{u} := by exact @HiddenMonotonicity.MaxPolynomial.ordinary_finite_polynomial_witness.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaxPolynomial.ordinary_finite_polynomial_witness
  let expected ← getConstInfo `_ThesisExactChecks.target_146
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaxPolynomial.ordinary_finite_polynomial_witness"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaxPolynomial.ordinary_finite_polynomial_witness | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.FinitePolynomialWitness do
    throwError "Defining module mismatch: HiddenMonotonicity.MaxPolynomial.ordinary_finite_polynomial_witness"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_146) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaxPolynomial.ordinary_finite_polynomial_witness: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaxPolynomial.ordinary_finite_polynomial_witness"
#check @HiddenMonotonicity.MaxPolynomial.ordinary_finite_polynomial_witness
#print axioms _ThesisExactChecks.target_146

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_147 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (x : Vec d) (i : Fin n),
 c.eval x i = (c.positiveExpressions.1 i).polynomialMaximum.eval (canonicalSplitInput x) -
 (c.positiveExpressions.2 i).polynomialMaximum.eval (canonicalSplitInput x))
theorem _ThesisExactChecks.target_147 : _ThesisExpectedTypes.type_147 := by exact @HiddenMonotonicity.Circuit.maxout_multiplication_split_correct
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Circuit.maxout_multiplication_split_correct
  let expected ← getConstInfo `_ThesisExactChecks.target_147
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Circuit.maxout_multiplication_split_correct"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Circuit.maxout_multiplication_split_correct | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.CircuitStatements do
    throwError "Defining module mismatch: HiddenMonotonicity.Circuit.maxout_multiplication_split_correct"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_147) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Circuit.maxout_multiplication_split_correct: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Circuit.maxout_multiplication_split_correct"
#check @HiddenMonotonicity.Circuit.maxout_multiplication_split_correct
#print axioms _ThesisExactChecks.target_147

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology
def _ThesisExpectedTypes.type_148 : Prop := ((∀ a : ModernActivation,
  let f := a.eval
  Differentiable ℝ f ∧
  (∀ l r, AbsolutelyContinuousOnInterval (deriv f) l r) ∧
  Integrable (curvature f) ∧ 0≤f 0 ∧
  Tendsto (deriv f) atBot (𝓝 (minusInfinitySlope f)) ∧
  (∃ B : ℝ, ∀ x, |deriv f x|≤B) ∧
  ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
  ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
  Monotone (tilt (C1 f) (commonTilt f)) ∧ Monotone (tilt (C2 f) (commonTilt f)) ∧
  (∀ z : ℝ × ℝ, tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2)) ∧
  NonnegativePairActivation (splitPair f)) ∧
(∀ x, curvature gaussianGelu x=(2-x^2)*standardGaussianDensity x ∧
  (0<curvature gaussianGelu x ↔ |x|<Real.sqrt 2) ∧
  (curvature gaussianGelu x<0 ↔ Real.sqrt 2< |x|)) ∧
(∀ β : ℝ, 0<β →
  (∀ x, curvature (swish β) x=β*sigmoidFirst (β*x)*(2+β*x*(1-2*Real.sigmoid (β*x)))) ∧
  ∃ ε R : ℝ, 0<ε ∧ 0<R ∧ (∀ x, |x|<ε → 0<curvature (swish β) x) ∧
    (∀ x, R< |x| → curvature (swish β) x<0)) ∧
(∀ x, mish x=x*Real.tanh (Real.log (1+Real.exp x))) ∧
(∀ x, curvature Real.tanh x=-2*Real.tanh x/(Real.cosh x)^2 ∧
  (0≤x → positiveCurvature Real.tanh x=0) ∧ (x≤0 → negativeCurvature Real.tanh x=0)) ∧
(∀ x, curvature Real.sigmoid x=sigmoidFirst x*(1-2*Real.sigmoid x)) ∧
(∀ θ : ℝ, 0<θ →
  (∀ x, curvature (Thesis.Regularization.softplus θ) x=sigmoidFirst (x/θ)/θ) ∧
  negativeCurvature (Thesis.Regularization.softplus θ)=0 ∧
  C2 (Thesis.Regularization.softplus θ)=0 ∧
  C1 (Thesis.Regularization.softplus θ)=Thesis.Regularization.softplus θ))
theorem _ThesisExactChecks.target_148 : _ThesisExpectedTypes.type_148 := by exact @HiddenMonotonicity.SmoothDC.modern_activations
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.modern_activations
  let expected ← getConstInfo `_ThesisExactChecks.target_148
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.modern_activations"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.modern_activations | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernActivations do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.modern_activations"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_148) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.modern_activations: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.modern_activations"
#check @HiddenMonotonicity.SmoothDC.modern_activations
#print axioms _ThesisExactChecks.target_148

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology
def _ThesisExpectedTypes.type_149 : Prop := (Integrable (curvature gaussianGelu) ∧
(∀ a b, AbsolutelyContinuousOnInterval (deriv gaussianGelu) a b) ∧
ConvexOn ℝ univ (tilt (C1 gaussianGelu) (commonTilt gaussianGelu)) ∧
ConvexOn ℝ univ (tilt (C2 gaussianGelu) (commonTilt gaussianGelu)) ∧
Monotone (tilt (C1 gaussianGelu) (commonTilt gaussianGelu)) ∧
Monotone (tilt (C2 gaussianGelu) (commonTilt gaussianGelu)) ∧
ValidPairActivation gaussianGelu (splitPair gaussianGelu) ∧
NonnegativePairActivation (splitPair gaussianGelu))
theorem _ThesisExactChecks.target_149 : _ThesisExpectedTypes.type_149 := by exact @HiddenMonotonicity.SmoothDC.gaussianGelu_smooth_dc_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.gaussianGelu_smooth_dc_split
  let expected ← getConstInfo `_ThesisExactChecks.target_149
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.gaussianGelu_smooth_dc_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.gaussianGelu_smooth_dc_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernGELU do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.gaussianGelu_smooth_dc_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_149) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.gaussianGelu_smooth_dc_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.gaussianGelu_smooth_dc_split"
#check @HiddenMonotonicity.SmoothDC.gaussianGelu_smooth_dc_split
#print axioms _ThesisExactChecks.target_149

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology
def _ThesisExpectedTypes.type_150 : Prop := (Integrable (curvature mish) ∧
(∀ a b, AbsolutelyContinuousOnInterval (deriv mish) a b) ∧
ConvexOn ℝ univ (tilt (C1 mish) (commonTilt mish)) ∧
ConvexOn ℝ univ (tilt (C2 mish) (commonTilt mish)) ∧
Monotone (tilt (C1 mish) (commonTilt mish)) ∧
Monotone (tilt (C2 mish) (commonTilt mish)) ∧
ValidPairActivation mish (splitPair mish) ∧
NonnegativePairActivation (splitPair mish))
theorem _ThesisExactChecks.target_150 : _ThesisExpectedTypes.type_150 := by exact @HiddenMonotonicity.SmoothDC.mish_smooth_dc_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.mish_smooth_dc_split
  let expected ← getConstInfo `_ThesisExactChecks.target_150
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.mish_smooth_dc_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.mish_smooth_dc_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernMish do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.mish_smooth_dc_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_150) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.mish_smooth_dc_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.mish_smooth_dc_split"
#check @HiddenMonotonicity.SmoothDC.mish_smooth_dc_split
#print axioms _ThesisExactChecks.target_150

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology
def _ThesisExpectedTypes.type_151 : Prop := (∀ (β : ℝ) (hβ : 0<β),
Integrable (curvature (swish β)) ∧
(∀ a b, AbsolutelyContinuousOnInterval (deriv (swish β)) a b) ∧
ConvexOn ℝ univ (tilt (C1 (swish β)) (commonTilt (swish β))) ∧
ConvexOn ℝ univ (tilt (C2 (swish β)) (commonTilt (swish β))) ∧
Monotone (tilt (C1 (swish β)) (commonTilt (swish β))) ∧
Monotone (tilt (C2 (swish β)) (commonTilt (swish β))) ∧
ValidPairActivation (swish β) (splitPair (swish β)) ∧
NonnegativePairActivation (splitPair (swish β)))
theorem _ThesisExactChecks.target_151 : _ThesisExpectedTypes.type_151 := by exact @HiddenMonotonicity.SmoothDC.swish_smooth_dc_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.swish_smooth_dc_split
  let expected ← getConstInfo `_ThesisExactChecks.target_151
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.swish_smooth_dc_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.swish_smooth_dc_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernSwish do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.swish_smooth_dc_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_151) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.swish_smooth_dc_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.swish_smooth_dc_split"
#check @HiddenMonotonicity.SmoothDC.swish_smooth_dc_split
#print axioms _ThesisExactChecks.target_151

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology ContDiff
def _ThesisExpectedTypes.type_152 : Prop := (∀ (f q : ℝ → ℝ)
(hf : Continuous f) (hw : HasSecondDistributionalDerivative f q),
Differentiable ℝ f ∧
(∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b) ∧
(∀ᵐ x, curvature f x=q x) ∧
∃ a b : ℝ, ∀ x, f x=localPrimitive (localPrimitive q) x+a*x+b)
theorem _ThesisExactChecks.target_152 : _ThesisExpectedTypes.type_152 := by exact @HiddenMonotonicity.SmoothDC.distributional_second_derivative_regular
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.distributional_second_derivative_regular
  let expected ← getConstInfo `_ThesisExactChecks.target_152
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.distributional_second_derivative_regular"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.distributional_second_derivative_regular | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.DistributionalRegularity do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.distributional_second_derivative_regular"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_152) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.distributional_second_derivative_regular: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.distributional_second_derivative_regular"
#check @HiddenMonotonicity.SmoothDC.distributional_second_derivative_regular
#print axioms _ThesisExactChecks.target_152

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology ContDiff
def _ThesisExpectedTypes.type_153 : Prop := (∀ (f c1 c2 q1 q2 : ℝ → ℝ)
(hf : Differentiable ℝ f)
(hfAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
(hq : Integrable (curvature f))
(hc1 : ConvexOn ℝ univ c1) (hc2 : ConvexOn ℝ univ c2)
(hw1 : HasSecondDistributionalDerivative c1 q1)
(hw2 : HasSecondDistributionalDerivative c2 q2)
(heq : ∀ x, f x=c1 x-c2 x),
Differentiable ℝ c1 ∧ Differentiable ℝ c2 ∧
(∀ a b, AbsolutelyContinuousOnInterval (deriv c1) a b) ∧
(∀ a b, AbsolutelyContinuousOnInterval (deriv c2) a b) ∧
(∀ᵐ x, curvature c1 x=q1 x ∧ curvature c2 x=q2 x) ∧
(∀ᵐ x, positiveCurvature f x≤q1 x ∧ negativeCurvature f x≤q2 x) ∧
((∀ᵐ x, q1 x=positiveCurvature f x ∧ q2 x=negativeCurvature f x) →
  ∃ a b : ℝ, (∀ x, c1 x=C1 f x+a*x+b) ∧ (∀ x, c2 x=C2 f x+a*x+b)) ∧
(∀ L, Monotone (tilt (C1 f) L) → Monotone (tilt (C2 f) L) → commonTilt f≤L))
theorem _ThesisExactChecks.target_153 : _ThesisExpectedTypes.type_153 := by exact @HiddenMonotonicity.SmoothDC.curvature_minimality_distributional
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.curvature_minimality_distributional
  let expected ← getConstInfo `_ThesisExactChecks.target_153
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.curvature_minimality_distributional"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.curvature_minimality_distributional | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.DistributionalRegularity do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.curvature_minimality_distributional"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_153) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.curvature_minimality_distributional: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.curvature_minimality_distributional"
#check @HiddenMonotonicity.SmoothDC.curvature_minimality_distributional
#print axioms _ThesisExactChecks.target_153

section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology ContDiff
def _ThesisExpectedTypes.type_154 : Prop := ((∀ a : ModernActivation,
  let f := a.eval
  Differentiable ℝ f ∧
  (∀ l r, AbsolutelyContinuousOnInterval (deriv f) l r) ∧
  Integrable (curvature f) ∧ 0≤f 0 ∧
  Tendsto (deriv f) atBot (𝓝 (minusInfinitySlope f)) ∧
  (∃ B : ℝ, ∀ x, |deriv f x|≤B) ∧
  ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
  ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
  Monotone (tilt (C1 f) (commonTilt f)) ∧ Monotone (tilt (C2 f) (commonTilt f)) ∧
  (∀ z : ℝ × ℝ, tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2)) ∧
  NonnegativePairActivation (splitPair f)) ∧
(∀ x, curvature gaussianGelu x=(2-x^2)*standardGaussianDensity x ∧
  (0<curvature gaussianGelu x ↔ |x|<Real.sqrt 2) ∧
  (curvature gaussianGelu x<0 ↔ Real.sqrt 2< |x|)) ∧
(∀ β : ℝ, 0<β →
  (∀ x, curvature (swish β) x=β*sigmoidFirst (β*x)*(2+β*x*(1-2*Real.sigmoid (β*x)))) ∧
  ∃ ε R : ℝ, 0<ε ∧ 0<R ∧ (∀ x, |x|<ε → 0<curvature (swish β) x) ∧
    (∀ x, R< |x| → curvature (swish β) x<0)) ∧
(∀ x, mish x=x*Real.tanh (Real.log (1+Real.exp x))) ∧
(∀ x, curvature Real.tanh x=-2*Real.tanh x/(Real.cosh x)^2 ∧
  (0≤x → positiveCurvature Real.tanh x=0) ∧ (x≤0 → negativeCurvature Real.tanh x=0)) ∧
(∀ x, curvature Real.sigmoid x=sigmoidFirst x*(1-2*Real.sigmoid x)) ∧
(∀ θ : ℝ, 0<θ →
  (∀ x, curvature (Thesis.Regularization.softplus θ) x=sigmoidFirst (x/θ)/θ ∧
    0≤curvature (Thesis.Regularization.softplus θ) x) ∧
  negativeCurvature (Thesis.Regularization.softplus θ)=0 ∧
  C2 (Thesis.Regularization.softplus θ)=0 ∧
  C1 (Thesis.Regularization.softplus θ)=Thesis.Regularization.softplus θ ∧
  ConvexOn ℝ univ (Thesis.Regularization.softplus θ)))
theorem _ThesisExactChecks.target_154 : _ThesisExpectedTypes.type_154 := by exact @HiddenMonotonicity.SmoothDC.modern_activations_complete
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.modern_activations_complete
  let expected ← getConstInfo `_ThesisExactChecks.target_154
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.modern_activations_complete"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.modern_activations_complete | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernActivationCorollary do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.modern_activations_complete"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_154) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.modern_activations_complete: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.modern_activations_complete"
#check @HiddenMonotonicity.SmoothDC.modern_activations_complete
#print axioms _ThesisExactChecks.target_154

section
open Finset Thesis.RoutingExtended
def _ThesisExpectedTypes.type_155 : Prop := (∀ (w : ℝ) (hw : 0 ≤ w) (v : WithBot ℝ),
    Thesis.RoutingGate.logCoordinate (w * expZero v) =
      Thesis.RoutingGate.logCoordinate w + v)
theorem _ThesisExactChecks.target_155 : _ThesisExpectedTypes.type_155 := by exact @Thesis.RoutingExtended.source_edge_score
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExtended.source_edge_score
  let expected ← getConstInfo `_ThesisExactChecks.target_155
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingExtended.source_edge_score"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExtended.source_edge_score | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExtended do
    throwError "Defining module mismatch: Thesis.RoutingExtended.source_edge_score"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_155) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingExtended.source_edge_score: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExtended.source_edge_score"
#check @Thesis.RoutingExtended.source_edge_score
#print axioms _ThesisExactChecks.target_155

section
universe u
open Finset Thesis.RoutingExtended
def _ThesisExpectedTypes.type_156 : Prop := (∀ {A : Type u} [Fintype A] (θ : ℝ) (p : Policy A),
    Monotone (fun m => routedMass θ m p))
theorem _ThesisExactChecks.target_156 : _ThesisExpectedTypes.type_156.{u} := by exact @Thesis.RoutingExtended.routedMass_monotone.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExtended.routedMass_monotone
  let expected ← getConstInfo `_ThesisExactChecks.target_156
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExtended.routedMass_monotone"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExtended.routedMass_monotone | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExtended do
    throwError "Defining module mismatch: Thesis.RoutingExtended.routedMass_monotone"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_156) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingExtended.routedMass_monotone: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExtended.routedMass_monotone"
#check @Thesis.RoutingExtended.routedMass_monotone
#print axioms _ThesisExactChecks.target_156

section
universe u
open Finset Thesis.RoutingExtended
def _ThesisExpectedTypes.type_157 : Prop := (∀ {A : Type u} [Fintype A] [DecidableEq A] (θ : ℝ) (hθ : 0 < θ)
    (m : A → ℝ) (outside : A) (p : Policy A),
    sourceValue θ m p ≤ sourceValue θ m (gibbs θ m outside))
theorem _ThesisExactChecks.target_157 : _ThesisExpectedTypes.type_157.{u} := by exact @Thesis.RoutingExtended.sourceValue_gibbs_optimal.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExtended.sourceValue_gibbs_optimal
  let expected ← getConstInfo `_ThesisExactChecks.target_157
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExtended.sourceValue_gibbs_optimal"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExtended.sourceValue_gibbs_optimal | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExtended do
    throwError "Defining module mismatch: Thesis.RoutingExtended.sourceValue_gibbs_optimal"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_157) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingExtended.sourceValue_gibbs_optimal: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExtended.sourceValue_gibbs_optimal"
#check @Thesis.RoutingExtended.sourceValue_gibbs_optimal
#print axioms _ThesisExactChecks.target_157

section
universe u
open Finset Thesis.RoutingExtended
def _ThesisExpectedTypes.type_158 : Prop := (∀ {A : Type u} [Fintype A] [DecidableEq A] (m : A → ℝ) (hm : ∀ i, 0 ≤ m i) (outside : A),
    routedMass 1 m (gibbs 1 m outside) = ∑ i, m i)
theorem _ThesisExactChecks.target_158 : _ThesisExpectedTypes.type_158.{u} := by exact @Thesis.RoutingExtended.gibbs_anchor_mass.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExtended.gibbs_anchor_mass
  let expected ← getConstInfo `_ThesisExactChecks.target_158
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExtended.gibbs_anchor_mass"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExtended.gibbs_anchor_mass | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExtended do
    throwError "Defining module mismatch: Thesis.RoutingExtended.gibbs_anchor_mass"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_158) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingExtended.gibbs_anchor_mass: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExtended.gibbs_anchor_mass"
#check @Thesis.RoutingExtended.gibbs_anchor_mass
#print axioms _ThesisExactChecks.target_158

section
universe u
open Finset Thesis.RoutingExtended
def _ThesisExpectedTypes.type_159 : Prop := (∀ {A : Type u} [Fintype A] [DecidableEq A] (m : A → ℝ) (hm : ∀ i, 0 ≤ m i)
    (outside i : A) (hi : i ≠ outside),
    (gibbs 1 m outside).prob i = m i / ∑ j, m j)
theorem _ThesisExactChecks.target_159 : _ThesisExpectedTypes.type_159.{u} := by exact @Thesis.RoutingExtended.gibbs_anchor_nonoutside.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExtended.gibbs_anchor_nonoutside
  let expected ← getConstInfo `_ThesisExactChecks.target_159
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExtended.gibbs_anchor_nonoutside"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExtended.gibbs_anchor_nonoutside | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExtended do
    throwError "Defining module mismatch: Thesis.RoutingExtended.gibbs_anchor_nonoutside"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_159) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingExtended.gibbs_anchor_nonoutside: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExtended.gibbs_anchor_nonoutside"
#check @Thesis.RoutingExtended.gibbs_anchor_nonoutside
#print axioms _ThesisExactChecks.target_159

section
universe u
open Finset Thesis.RoutingExtended
def _ThesisExpectedTypes.type_160 : Prop := (∀ {A : Type u} [Fintype A] (θ : ℝ) (m : A → ℝ) (p : Policy A) (hm : ∀ i, m i ≤ 0),
    sourceValue θ m p = ⊥ ∧ routedMass θ m p = 0)
theorem _ThesisExactChecks.target_160 : _ThesisExpectedTypes.type_160.{u} := by exact @Thesis.RoutingExtended.empty_stream_value.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExtended.empty_stream_value
  let expected ← getConstInfo `_ThesisExactChecks.target_160
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExtended.empty_stream_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExtended.empty_stream_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExtended do
    throwError "Defining module mismatch: Thesis.RoutingExtended.empty_stream_value"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_160) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingExtended.empty_stream_value: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExtended.empty_stream_value"
#check @Thesis.RoutingExtended.empty_stream_value
#print axioms _ThesisExactChecks.target_160

section
universe u
open Finset Thesis.RoutingExtended
def _ThesisExpectedTypes.type_161 : Prop := (∀ {A : Type u} [Fintype A] [DecidableEq A] (θ : ℝ) (m : A → ℝ) (outside : A)
    (hm : ∀ i, m i ≤ 0),
    gibbs θ m outside = pure outside)
theorem _ThesisExactChecks.target_161 : _ThesisExpectedTypes.type_161.{u} := by exact @Thesis.RoutingExtended.empty_stream_absorbs.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExtended.empty_stream_absorbs
  let expected ← getConstInfo `_ThesisExactChecks.target_161
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExtended.empty_stream_absorbs"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExtended.empty_stream_absorbs | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExtended do
    throwError "Defining module mismatch: Thesis.RoutingExtended.empty_stream_absorbs"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_161) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingExtended.empty_stream_absorbs: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExtended.empty_stream_absorbs"
#check @Thesis.RoutingExtended.empty_stream_absorbs
#print axioms _ThesisExactChecks.target_161

section
open Thesis.RoutingExtended Thesis.RoutingProfiles
def _ThesisExpectedTypes.type_162 : Prop := (∀ (θ : ℝ) (hθ : 0 < θ) (t : Tree) (plus minus : Strategy t),
    auxiliary θ t plus (canonical θ t) ≤ value θ t ∧
      value θ t ≤ auxiliary θ t (canonical θ t) minus)
theorem _ThesisExactChecks.target_162 : _ThesisExpectedTypes.type_162 := by exact @Thesis.RoutingProfiles.auxiliary_saddle
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingProfiles.auxiliary_saddle
  let expected ← getConstInfo `_ThesisExactChecks.target_162
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingProfiles.auxiliary_saddle"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingProfiles.auxiliary_saddle | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingProfiles do
    throwError "Defining module mismatch: Thesis.RoutingProfiles.auxiliary_saddle"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_162) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingProfiles.auxiliary_saddle: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingProfiles.auxiliary_saddle"
#check @Thesis.RoutingProfiles.auxiliary_saddle
#print axioms _ThesisExactChecks.target_162

section
open Thesis.RoutingExtended Thesis.RoutingProfiles
def _ThesisExpectedTypes.type_163 : Prop := (∀ (θ : ℝ) (t : Tree) (plus minus : Strategy t),
    reported θ t plus minus =
      (Thesis.RoutingGate.logCoordinate (auxiliary θ t plus minus),
       Thesis.RoutingGate.logCoordinate (-auxiliary θ t plus minus)))
theorem _ThesisExactChecks.target_163 : _ThesisExpectedTypes.type_163 := by exact @Thesis.RoutingProfiles.reported_coordinates
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingProfiles.reported_coordinates
  let expected ← getConstInfo `_ThesisExactChecks.target_163
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingProfiles.reported_coordinates"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingProfiles.reported_coordinates | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingProfiles do
    throwError "Defining module mismatch: Thesis.RoutingProfiles.reported_coordinates"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_163) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingProfiles.reported_coordinates: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingProfiles.reported_coordinates"
#check @Thesis.RoutingProfiles.reported_coordinates
#print axioms _ThesisExactChecks.target_163

section
open Thesis.RoutingExtended Thesis.RoutingProfiles
def _ThesisExpectedTypes.type_164 : Prop := (∀ (θ : ℝ) (t : Tree) (plus minus : Strategy t),
    auxiliary θ t plus minus =
      expZero (reported θ t plus minus).1 - expZero (reported θ t plus minus).2)
theorem _ThesisExactChecks.target_164 : _ThesisExpectedTypes.type_164 := by exact @Thesis.RoutingProfiles.auxiliary_eq_reported_difference
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingProfiles.auxiliary_eq_reported_difference
  let expected ← getConstInfo `_ThesisExactChecks.target_164
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingProfiles.auxiliary_eq_reported_difference"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingProfiles.auxiliary_eq_reported_difference | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingProfiles do
    throwError "Defining module mismatch: Thesis.RoutingProfiles.auxiliary_eq_reported_difference"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_164) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingProfiles.auxiliary_eq_reported_difference: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingProfiles.auxiliary_eq_reported_difference"
#check @Thesis.RoutingProfiles.auxiliary_eq_reported_difference
#print axioms _ThesisExactChecks.target_164

section
open Thesis.RoutingExtended Thesis.RoutingProfiles
def _ThesisExpectedTypes.type_165 : Prop := (∀ (θ : ℝ) (hθ : 0 < θ) (t : Tree),
    IsNash θ t (canonical θ t))
theorem _ThesisExactChecks.target_165 : _ThesisExpectedTypes.type_165 := by exact @Thesis.RoutingProfiles.canonical_nash
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingProfiles.canonical_nash
  let expected ← getConstInfo `_ThesisExactChecks.target_165
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingProfiles.canonical_nash"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingProfiles.canonical_nash | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingProfiles do
    throwError "Defining module mismatch: Thesis.RoutingProfiles.canonical_nash"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_165) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingProfiles.canonical_nash: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingProfiles.canonical_nash"
#check @Thesis.RoutingProfiles.canonical_nash
#print axioms _ThesisExactChecks.target_165

section
open Thesis.RoutingExtended Thesis.RoutingProfiles
def _ThesisExpectedTypes.type_166 : Prop := (∀ (θ : ℝ) (hθ : 0 < θ) (t : Tree),
    IsSubgamePerfect θ t (canonical θ t))
theorem _ThesisExactChecks.target_166 : _ThesisExpectedTypes.type_166 := by exact @Thesis.RoutingProfiles.canonical_subgame_perfect
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingProfiles.canonical_subgame_perfect
  let expected ← getConstInfo `_ThesisExactChecks.target_166
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingProfiles.canonical_subgame_perfect"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingProfiles.canonical_subgame_perfect | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingProfiles do
    throwError "Defining module mismatch: Thesis.RoutingProfiles.canonical_subgame_perfect"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_166) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingProfiles.canonical_subgame_perfect: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingProfiles.canonical_subgame_perfect"
#check @Thesis.RoutingProfiles.canonical_subgame_perfect
#print axioms _ThesisExactChecks.target_166

section
open Thesis.RoutingExtended Thesis.RoutingProfiles
def _ThesisExpectedTypes.type_167 : Prop := (∀ (θ : ℝ) (q : Bool) (p n : Tree)
    (h : signed q (value θ p + value θ n) ≤ 0),
    (canonical θ (.activation q p n)).1 = false)
theorem _ThesisExactChecks.target_167 : _ThesisExpectedTypes.type_167 := by exact @Thesis.RoutingProfiles.canonical_stops_log_ties
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingProfiles.canonical_stops_log_ties
  let expected ← getConstInfo `_ThesisExactChecks.target_167
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingProfiles.canonical_stops_log_ties"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingProfiles.canonical_stops_log_ties | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingProfiles do
    throwError "Defining module mismatch: Thesis.RoutingProfiles.canonical_stops_log_ties"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_167) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingProfiles.canonical_stops_log_ties: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingProfiles.canonical_stops_log_ties"
#check @Thesis.RoutingProfiles.canonical_stops_log_ties
#print axioms _ThesisExactChecks.target_167

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
def _ThesisExpectedTypes.type_168 : Prop := (∀ {n} (q : Bool) (ε b : ℝ) (w a : Fin n → ℝ)
    (child : Fin n → Tree) (ha : ∀ i, 0 ≤ a i)
    (hv : ∀ i, value 1 (child i) = signed q (a i)),
    actionMass q (extend ε b w)
      (fun i => value 1 (extend (.terminal (signed q 1)) (.terminal (signed q 1)) child i)) =
      extend ε b (fun i => w i * a i))
theorem _ThesisExactChecks.target_168 : _ThesisExpectedTypes.type_168 := by exact @Thesis.RoutingNetwork.route_action_masses
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.route_action_masses
  let expected ← getConstInfo `_ThesisExactChecks.target_168
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.route_action_masses"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.route_action_masses | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.route_action_masses"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_168) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingNetwork.route_action_masses: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.route_action_masses"
#check @Thesis.RoutingNetwork.route_action_masses
#print axioms _ThesisExactChecks.target_168

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
def _ThesisExpectedTypes.type_169 : Prop := (∀ {n} (q : Bool) (ε b : ℝ) (w a : Fin n → ℝ)
    (child : Fin n → Tree) (hε : 0 ≤ ε) (hb : 0 ≤ b) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, value 1 (child i) = signed q (a i)),
    value 1 (route q ε b w child hε hb hw) = signed q (ε + (b + ∑ i, w i * a i)))
theorem _ThesisExactChecks.target_169 : _ThesisExpectedTypes.type_169 := by exact @Thesis.RoutingNetwork.route_anchor_value
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.route_anchor_value
  let expected ← getConstInfo `_ThesisExactChecks.target_169
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.route_anchor_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.route_anchor_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.route_anchor_value"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_169) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingNetwork.route_anchor_value: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.route_anchor_value"
#check @Thesis.RoutingNetwork.route_anchor_value
#print axioms _ThesisExactChecks.target_169

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
def _ThesisExpectedTypes.type_170 : Prop := (∀ {n} (q : Bool) (ε b : ℝ) (w a : Fin n → ℝ)
    (child : Fin n → Tree) (hε : 0 ≤ ε) (hb : 0 ≤ b) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, value 1 (child i) = signed q (a i)) (i : Fin n),
    (canonical 1 (route q ε b w child hε hb hw)).1.prob i.succ.succ =
      w i * a i / (ε + (b + ∑ j, w j * a j)))
theorem _ThesisExactChecks.target_170 : _ThesisExpectedTypes.type_170 := by exact @Thesis.RoutingNetwork.route_anchor_ordinary_probability
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.route_anchor_ordinary_probability
  let expected ← getConstInfo `_ThesisExactChecks.target_170
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.route_anchor_ordinary_probability"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.route_anchor_ordinary_probability | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.route_anchor_ordinary_probability"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_170) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingNetwork.route_anchor_ordinary_probability: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.route_anchor_ordinary_probability"
#check @Thesis.RoutingNetwork.route_anchor_ordinary_probability
#print axioms _ThesisExactChecks.target_170

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
def _ThesisExpectedTypes.type_171 : Prop := (∀ {n m} (net : Network n m) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (q : Bool),
    value 1 (networkGame net ε hε x j q) = signed q (net.eval x j))
theorem _ThesisExactChecks.target_171 : _ThesisExpectedTypes.type_171 := by exact @Thesis.RoutingNetwork.networkGame_value
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.networkGame_value
  let expected ← getConstInfo `_ThesisExactChecks.target_171
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.networkGame_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.networkGame_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.networkGame_value"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_171) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingNetwork.networkGame_value: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.networkGame_value"
#check @Thesis.RoutingNetwork.networkGame_value
#print axioms _ThesisExactChecks.target_171

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
def _ThesisExpectedTypes.type_172 : Prop := (∀ {n m} (net : Network n m) (θ : ℝ) (hθ : 0 < θ)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin m) (q : Bool),
    IsSubgamePerfect θ (networkGame net ε hε x j q) (canonical θ (networkGame net ε hε x j q)))
theorem _ThesisExactChecks.target_172 : _ThesisExpectedTypes.type_172 := by exact @Thesis.RoutingNetwork.networkGame_subgame_perfect
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.networkGame_subgame_perfect
  let expected ← getConstInfo `_ThesisExactChecks.target_172
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.networkGame_subgame_perfect"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.networkGame_subgame_perfect | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.networkGame_subgame_perfect"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_172) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingNetwork.networkGame_subgame_perfect: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.networkGame_subgame_perfect"
#check @Thesis.RoutingNetwork.networkGame_subgame_perfect
#print axioms _ThesisExactChecks.target_172

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
def _ThesisExpectedTypes.type_173 : Prop := (∀ {n m} (net : Network n m) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (q : Bool),
    reported 1 (networkGame net ε hε x j q)
      (canonical 1 (networkGame net ε hε x j q)) (canonical 1 (networkGame net ε hε x j q)) =
      (Thesis.RoutingGate.logCoordinate (signed q (net.eval x j)),
       Thesis.RoutingGate.logCoordinate (-signed q (net.eval x j))))
theorem _ThesisExactChecks.target_173 : _ThesisExpectedTypes.type_173 := by exact @Thesis.RoutingNetwork.networkGame_reported
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.networkGame_reported
  let expected ← getConstInfo `_ThesisExactChecks.target_173
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.networkGame_reported"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.networkGame_reported | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.networkGame_reported"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_173) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingNetwork.networkGame_reported: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.networkGame_reported"
#check @Thesis.RoutingNetwork.networkGame_reported
#print axioms _ThesisExactChecks.target_173

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
def _ThesisExpectedTypes.type_174 : Prop := (∀ {n k m} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (tail : Network k m) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (q : Bool),
    reported 1 (networkGame (.layer wp wn bp bn tail) ε hε x j q)
      (canonical 1 (networkGame (.layer wp wn bp bn tail) ε hε x j q))
      (canonical 1 (networkGame (.layer wp wn bp bn tail) ε hε x j q)) =
      if q then (Thesis.RoutingGate.logCoordinate ((Network.layer wp wn bp bn tail).eval x j), ⊥)
      else (⊥, Thesis.RoutingGate.logCoordinate ((Network.layer wp wn bp bn tail).eval x j)))
theorem _ThesisExactChecks.target_174 : _ThesisExpectedTypes.type_174 := by exact @Thesis.RoutingNetwork.networkLayer_reported
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.networkLayer_reported
  let expected ← getConstInfo `_ThesisExactChecks.target_174
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.networkLayer_reported"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.networkLayer_reported | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.networkLayer_reported"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_174) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingNetwork.networkLayer_reported: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.networkLayer_reported"
#check @Thesis.RoutingNetwork.networkLayer_reported
#print axioms _ThesisExactChecks.target_174

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
def _ThesisExpectedTypes.type_175 : Prop := (∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) (q : Bool),
    (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q)).1 =
      decide (0 < preactivation wp wn bp bn x j))
theorem _ThesisExactChecks.target_175 : _ThesisExpectedTypes.type_175 := by exact @Thesis.RoutingNetwork.inputLayerGames_selected_gate
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.inputLayerGames_selected_gate
  let expected ← getConstInfo `_ThesisExactChecks.target_175
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.inputLayerGames_selected_gate"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.inputLayerGames_selected_gate | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.inputLayerGames_selected_gate"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_175) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingNetwork.inputLayerGames_selected_gate: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.inputLayerGames_selected_gate"
#check @Thesis.RoutingNetwork.inputLayerGames_selected_gate
#print axioms _ThesisExactChecks.target_175

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
def _ThesisExpectedTypes.type_176 : Prop := (∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (input : Fin n → Bool → Tree) (x : Vec n)
    (hx : ∀ i, 0 ≤ x i) (hv : ∀ i q, value 1 (input i q) = signed q (x i))
    (j : Fin k) (q : Bool),
    (canonical 1 (layerGames wp wn bp bn ε hε input j q)).1 =
      decide (0 < preactivation wp wn bp bn x j))
theorem _ThesisExactChecks.target_176 : _ThesisExpectedTypes.type_176 := by exact @Thesis.RoutingNetwork.layerGames_selected_gate
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.layerGames_selected_gate
  let expected ← getConstInfo `_ThesisExactChecks.target_176
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.layerGames_selected_gate"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.layerGames_selected_gate | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.layerGames_selected_gate"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_176) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingNetwork.layerGames_selected_gate: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.layerGames_selected_gate"
#check @Thesis.RoutingNetwork.layerGames_selected_gate
#print axioms _ThesisExactChecks.target_176

section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingStructure
open scoped BigOperators
def _ThesisExpectedTypes.type_177 : Prop := (∀ {n m : ℕ} (net : Network n m) (hp : net.NonnegativeParameters) (r : Vec n),
 0≤frozenStopping net r 0 ∧ Monotone (stoppingJac (net.originalTrace r)) ∧
 (∀ x ∈ gateRegion net r, net.decomposeWith stopPair x = stoppingJac (net.originalTrace r) x + frozenStopping net r 0) ∧
 MonotoneOn (net.decomposeWith stopPair) (gateRegion net r))
theorem _ThesisExactChecks.target_177 : _ThesisExpectedTypes.type_177 := by exact @Thesis.StoppingStructure.stopping_region_nonnegative_affine
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingStructure.stopping_region_nonnegative_affine
  let expected ← getConstInfo `_ThesisExactChecks.target_177
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingStructure.stopping_region_nonnegative_affine"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingStructure.stopping_region_nonnegative_affine | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingRegions do
    throwError "Defining module mismatch: Thesis.StoppingStructure.stopping_region_nonnegative_affine"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_177) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingStructure.stopping_region_nonnegative_affine: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingStructure.stopping_region_nonnegative_affine"
#check @Thesis.StoppingStructure.stopping_region_nonnegative_affine
#print axioms _ThesisExactChecks.target_177

section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingStructure
open scoped BigOperators
def _ThesisExpectedTypes.type_178 : Prop := (∀ {n m : ℕ} (net : Network n m) (x : PairVec n),
 net.decomposeWith stopPair x = stoppingJac (net.originalTrace (x.1-x.2)) x + (biasSources net (x.1-x.2)).sum)
theorem _ThesisExactChecks.target_178 : _ThesisExpectedTypes.type_178 := by exact @Thesis.StoppingStructure.stopping_input_and_bias_sources
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingStructure.stopping_input_and_bias_sources
  let expected ← getConstInfo `_ThesisExactChecks.target_178
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingStructure.stopping_input_and_bias_sources"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingStructure.stopping_input_and_bias_sources | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingRegions do
    throwError "Defining module mismatch: Thesis.StoppingStructure.stopping_input_and_bias_sources"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_178) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingStructure.stopping_input_and_bias_sources: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingStructure.stopping_input_and_bias_sources"
#check @Thesis.StoppingStructure.stopping_input_and_bias_sources
#print axioms _ThesisExactChecks.target_178

section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingStructure
open scoped BigOperators
def _ThesisExpectedTypes.type_179 : Prop := (∀ {n m : ℕ} (tr : MaskedTrace n m) (i : Fin n) (path : GeometricPaths tr),
 geometricParity tr i path = decide (Odd (negativeEdgeCount tr i path)))
theorem _ThesisExactChecks.target_179 : _ThesisExpectedTypes.type_179 := by exact @Thesis.StoppingStructure.geometricParity_negative_count
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingStructure.geometricParity_negative_count
  let expected ← getConstInfo `_ThesisExactChecks.target_179
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingStructure.geometricParity_negative_count"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingStructure.geometricParity_negative_count | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingPaths do
    throwError "Defining module mismatch: Thesis.StoppingStructure.geometricParity_negative_count"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_179) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingStructure.geometricParity_negative_count: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingStructure.geometricParity_negative_count"
#check @Thesis.StoppingStructure.geometricParity_negative_count
#print axioms _ThesisExactChecks.target_179

section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingStructure
open scoped BigOperators
def _ThesisExpectedTypes.type_180 : Prop := (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (hb : ZeroBias net) (x : PairVec n) (j : Fin m),
 let tr := net.originalTrace (x.1-x.2)
 (net.decomposeWith stopPair x).1 j = ∑ i, ∑ path : GeometricPaths tr,
 geometricWeight tr j i path * (if geometricParity tr i path then x.2 i else x.1 i) ∧
 (net.decomposeWith stopPair x).2 j = ∑ i, ∑ path : GeometricPaths tr,
 geometricWeight tr j i path * (if geometricParity tr i path then x.1 i else x.2 i))
theorem _ThesisExactChecks.target_180 : _ThesisExpectedTypes.type_180 := by exact @Thesis.StoppingStructure.stopping_activation_parity_paths
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingStructure.stopping_activation_parity_paths
  let expected ← getConstInfo `_ThesisExactChecks.target_180
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingStructure.stopping_activation_parity_paths"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingStructure.stopping_activation_parity_paths | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingPaths do
    throwError "Defining module mismatch: Thesis.StoppingStructure.stopping_activation_parity_paths"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_180) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingStructure.stopping_activation_parity_paths: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingStructure.stopping_activation_parity_paths"
#check @Thesis.StoppingStructure.stopping_activation_parity_paths
#print axioms _ThesisExactChecks.target_180

section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingStructure
open scoped BigOperators
def _ThesisExpectedTypes.type_181 : Prop := (∀ {n m k : ℕ} (net : Network n m) (hc : net.Canonical) (hb : ZeroBias net)
 (wp wn : Matrix (Fin k) (Fin m) ℝ)
 (hw : ∀ j i, wp j i=max (wp j i-wn j i) 0 ∧ wn j i=max (-(wp j i-wn j i)) 0)
 (x : PairVec n) (j : Fin k),
 let tr := preactivationTrace net (x.1-x.2) wp wn
 preP wp wn (net.decomposeWith stopPair x) j = ∑ i, ∑ path : GeometricPaths tr,
 geometricWeight tr j i path * (if geometricParity tr i path then x.2 i else x.1 i) ∧
 preN wp wn (net.decomposeWith stopPair x) j = ∑ i, ∑ path : GeometricPaths tr,
 geometricWeight tr j i path * (if geometricParity tr i path then x.1 i else x.2 i))
theorem _ThesisExactChecks.target_181 : _ThesisExpectedTypes.type_181 := by exact @Thesis.StoppingStructure.stopping_preactivation_parity_paths
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingStructure.stopping_preactivation_parity_paths
  let expected ← getConstInfo `_ThesisExactChecks.target_181
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingStructure.stopping_preactivation_parity_paths"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingStructure.stopping_preactivation_parity_paths | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingPaths do
    throwError "Defining module mismatch: Thesis.StoppingStructure.stopping_preactivation_parity_paths"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_181) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingStructure.stopping_preactivation_parity_paths: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingStructure.stopping_preactivation_parity_paths"
#check @Thesis.StoppingStructure.stopping_preactivation_parity_paths
#print axioms _ThesisExactChecks.target_181

section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingStructure
open scoped BigOperators
def _ThesisExpectedTypes.type_182 : Prop := (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (x : PairVec n) (j : Fin m),
 let tr := net.originalTrace (x.1-x.2)
 (net.decomposeWith stopPair x).1 j =
 (∑ i, ∑ path : GeometricPaths tr, geometricWeight tr j i path * (if geometricParity tr i path then x.2 i else x.1 i)) + ((biasSources net (x.1-x.2)).sum).1 j ∧
 (net.decomposeWith stopPair x).2 j =
 (∑ i, ∑ path : GeometricPaths tr, geometricWeight tr j i path * (if geometricParity tr i path then x.1 i else x.2 i)) + ((biasSources net (x.1-x.2)).sum).2 j)
theorem _ThesisExactChecks.target_182 : _ThesisExpectedTypes.type_182 := by exact @Thesis.StoppingStructure.stopping_biased_parity_paths
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingStructure.stopping_biased_parity_paths
  let expected ← getConstInfo `_ThesisExactChecks.target_182
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingStructure.stopping_biased_parity_paths"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingStructure.stopping_biased_parity_paths | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingPaths do
    throwError "Defining module mismatch: Thesis.StoppingStructure.stopping_biased_parity_paths"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_182) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingStructure.stopping_biased_parity_paths: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingStructure.stopping_biased_parity_paths"
#check @Thesis.StoppingStructure.stopping_biased_parity_paths
#print axioms _ThesisExactChecks.target_182

section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_183 : Prop := (∀ {n : ℕ} (a : SignedExpr (Fin n)) (x : PairVec n),
 stoppingExpr (.maximum a (.constant 0)) x = stopPair (stoppingExpr a x))
theorem _ThesisExactChecks.target_183 : _ThesisExpectedTypes.type_183 := by exact @Thesis.StoppingCircuit.stoppingExpr_relu
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingCircuit.stoppingExpr_relu
  let expected ← getConstInfo `_ThesisExactChecks.target_183
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingCircuit.stoppingExpr_relu"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingCircuit.stoppingExpr_relu | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingCircuit do
    throwError "Defining module mismatch: Thesis.StoppingCircuit.stoppingExpr_relu"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_183) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingCircuit.stoppingExpr_relu: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingCircuit.stoppingExpr_relu"
#check @Thesis.StoppingCircuit.stoppingExpr_relu
#print axioms _ThesisExactChecks.target_183

section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_184 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (x : PairVec d),
 (stoppingCircuit c x).1-(stoppingCircuit c x).2 = c.eval (x.1-x.2))
theorem _ThesisExactChecks.target_184 : _ThesisExpectedTypes.type_184 := by exact @Thesis.StoppingCircuit.stoppingCircuit_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingCircuit.stoppingCircuit_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_184
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingCircuit.stoppingCircuit_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingCircuit.stoppingCircuit_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingCircuit do
    throwError "Defining module mismatch: Thesis.StoppingCircuit.stoppingCircuit_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_184) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingCircuit.stoppingCircuit_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingCircuit.stoppingCircuit_recovery"
#check @Thesis.StoppingCircuit.stoppingCircuit_recovery
#print axioms _ThesisExactChecks.target_184

section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_185 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (x : PairVec d) (hx : 0≤x),
 0≤stoppingCircuit c x)
theorem _ThesisExactChecks.target_185 : _ThesisExpectedTypes.type_185 := by exact @Thesis.StoppingCircuit.stoppingCircuit_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingCircuit.stoppingCircuit_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_185
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingCircuit.stoppingCircuit_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingCircuit.stoppingCircuit_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingCircuit do
    throwError "Defining module mismatch: Thesis.StoppingCircuit.stoppingCircuit_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_185) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingCircuit.stoppingCircuit_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingCircuit.stoppingCircuit_nonnegative"
#check @Thesis.StoppingCircuit.stoppingCircuit_nonnegative
#print axioms _ThesisExactChecks.target_185

section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_186 : Prop := ((∀ b, 0≤additionProbability b) ∧ (∑ b : Bool, additionProbability b)=1)
theorem _ThesisExactChecks.target_186 : _ThesisExpectedTypes.type_186 := by exact @Thesis.StoppingCircuit.addition_probability_law
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingCircuit.addition_probability_law
  let expected ← getConstInfo `_ThesisExactChecks.target_186
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingCircuit.addition_probability_law"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingCircuit.addition_probability_law | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingCircuit do
    throwError "Defining module mismatch: Thesis.StoppingCircuit.addition_probability_law"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_186) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingCircuit.addition_probability_law: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingCircuit.addition_probability_law"
#check @Thesis.StoppingCircuit.addition_probability_law
#print axioms _ThesisExactChecks.target_186

section
universe u
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_187 : Prop := (∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
 (f g : E → ℝ) (Df Dg : E →L[ℝ] ℝ) (x : E)
 (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x),
 HasFDerivAt (fun y => f y+g y) ((2 : ℝ) • (additionProbability false • Df+additionProbability true • Dg)) x)
theorem _ThesisExactChecks.target_187 : _ThesisExpectedTypes.type_187.{u} := by exact @Thesis.StoppingCircuit.addition_derivative_occupation.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingCircuit.addition_derivative_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_187
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.StoppingCircuit.addition_derivative_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingCircuit.addition_derivative_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingCircuit do
    throwError "Defining module mismatch: Thesis.StoppingCircuit.addition_derivative_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_187) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingCircuit.addition_derivative_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingCircuit.addition_derivative_occupation"
#check @Thesis.StoppingCircuit.addition_derivative_occupation
#print axioms _ThesisExactChecks.target_187

section
universe u
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_188 : Prop := (∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
 (f g : E → ℝ × ℝ) (Df Dg : E →L[ℝ] ℝ × ℝ) (x : E)
 (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x)
 (hne : (f x).1-(f x).2 ≠ (g x).1-(g x).2),
 HasFDerivAt (fun y => winnerPair (g y) (f y))
 (if (g x).1-(g x).2 < (f x).1-(f x).2 then Df else Dg) x)
theorem _ThesisExactChecks.target_188 : _ThesisExpectedTypes.type_188.{u} := by exact @Thesis.StoppingCircuit.winner_derivative.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingCircuit.winner_derivative
  let expected ← getConstInfo `_ThesisExactChecks.target_188
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.StoppingCircuit.winner_derivative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingCircuit.winner_derivative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingCircuit do
    throwError "Defining module mismatch: Thesis.StoppingCircuit.winner_derivative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_188) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingCircuit.winner_derivative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingCircuit.winner_derivative"
#check @Thesis.StoppingCircuit.winner_derivative
#print axioms _ThesisExactChecks.target_188

section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_189 : Prop := (∀ (leftWins : Bool),
 (∀ b,0≤winnerProbability leftWins b) ∧ (∑ b : Bool,winnerProbability leftWins b)=1)
theorem _ThesisExactChecks.target_189 : _ThesisExpectedTypes.type_189 := by exact @Thesis.StoppingCircuit.winner_probability_law
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingCircuit.winner_probability_law
  let expected ← getConstInfo `_ThesisExactChecks.target_189
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingCircuit.winner_probability_law"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingCircuit.winner_probability_law | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingCircuit do
    throwError "Defining module mismatch: Thesis.StoppingCircuit.winner_probability_law"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_189) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingCircuit.winner_probability_law: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingCircuit.winner_probability_law"
#check @Thesis.StoppingCircuit.winner_probability_law
#print axioms _ThesisExactChecks.target_189

section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_190 : Prop := (∀ (leftWins : Bool) (left right : ℝ),
 (1 : ℝ)*(winnerProbability leftWins true*left+winnerProbability leftWins false*right) = if leftWins then left else right)
theorem _ThesisExactChecks.target_190 : _ThesisExpectedTypes.type_190 := by exact @Thesis.StoppingCircuit.winner_discounted_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingCircuit.winner_discounted_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_190
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingCircuit.winner_discounted_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingCircuit.winner_discounted_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingCircuit do
    throwError "Defining module mismatch: Thesis.StoppingCircuit.winner_discounted_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_190) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingCircuit.winner_discounted_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingCircuit.winner_discounted_occupation"
#check @Thesis.StoppingCircuit.winner_discounted_occupation
#print axioms _ThesisExactChecks.target_190

section
universe u
open HiddenMonotonicity Thesis.StoppingCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_191 : Prop := (∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
 (f g : E → ℝ × ℝ) (Df Dg : E →L[ℝ] ℝ × ℝ) (x : E)
 (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x)
 (hne : (f x).1-(f x).2 ≠ (g x).1-(g x).2),
 HasFDerivAt (fun y => winnerPair (g y) (f y))
 ((1 : ℝ) • (winnerProbability (decide ((g x).1-(g x).2 < (f x).1-(f x).2)) true • Df +
 winnerProbability (decide ((g x).1-(g x).2 < (f x).1-(f x).2)) false • Dg)) x)
theorem _ThesisExactChecks.target_191 : _ThesisExpectedTypes.type_191.{u} := by exact @Thesis.StoppingCircuit.winner_derivative_occupation.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingCircuit.winner_derivative_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_191
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.StoppingCircuit.winner_derivative_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingCircuit.winner_derivative_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingCircuit do
    throwError "Defining module mismatch: Thesis.StoppingCircuit.winner_derivative_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_191) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingCircuit.winner_derivative_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingCircuit.winner_derivative_occupation"
#check @Thesis.StoppingCircuit.winner_derivative_occupation
#print axioms _ThesisExactChecks.target_191

section
open Set Filter Matrix Finset Thesis.Tropical Thesis.PiecewiseLinear
open scoped Topology
def _ThesisExpectedTypes.type_192 : Prop := (∀ {A : Type} [Fintype A] (f : ℝ → ℝ) (a b : A → ℝ)
(hf : Continuous f) (hsel : ∀ t, ∃ i, f t=(1-t)*a i+t*b i),
∃ i, f 0≤a i ∧ b i≤f 1)
theorem _ThesisExactChecks.target_192 : _ThesisExpectedTypes.type_192 := by exact @Thesis.PiecewiseLinear.affine_selection_separation
end
run_cmd do
  let target ← getConstInfo `Thesis.PiecewiseLinear.affine_selection_separation
  let expected ← getConstInfo `_ThesisExactChecks.target_192
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.PiecewiseLinear.affine_selection_separation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.PiecewiseLinear.affine_selection_separation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.CPWLLattice do
    throwError "Defining module mismatch: Thesis.PiecewiseLinear.affine_selection_separation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_192) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.PiecewiseLinear.affine_selection_separation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.PiecewiseLinear.affine_selection_separation"
#check @Thesis.PiecewiseLinear.affine_selection_separation
#print axioms _ThesisExactChecks.target_192

section
open Set Filter Matrix Finset Thesis.Tropical Thesis.PiecewiseLinear
open scoped Topology
def _ThesisExpectedTypes.type_193 : Prop := (∀ {I : Type} [Fintype I] (f : (I → ℝ) → ℝ)
(hf : CPWL (fun x (_ : Unit) => f x)),
∃ p : MaxMinPolynomial I, ∀ x, f x=p.eval x)
theorem _ThesisExactChecks.target_193 : _ThesisExpectedTypes.type_193 := by exact @Thesis.PiecewiseLinear.cpwl_lattice_representation
end
run_cmd do
  let target ← getConstInfo `Thesis.PiecewiseLinear.cpwl_lattice_representation
  let expected ← getConstInfo `_ThesisExactChecks.target_193
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.PiecewiseLinear.cpwl_lattice_representation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.PiecewiseLinear.cpwl_lattice_representation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.CPWLLattice do
    throwError "Defining module mismatch: Thesis.PiecewiseLinear.cpwl_lattice_representation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_193) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.PiecewiseLinear.cpwl_lattice_representation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.PiecewiseLinear.cpwl_lattice_representation"
#check @Thesis.PiecewiseLinear.cpwl_lattice_representation
#print axioms _ThesisExactChecks.target_193

section
open Set Filter Matrix Finset Thesis.Tropical Thesis.PiecewiseLinear
open scoped Topology
def _ThesisExpectedTypes.type_194 : Prop := (∀ {I : Type} [Fintype I] (f : (I → ℝ) → ℝ)
(hf : CPWL (fun x (_ : Unit) => f x)),
∃ g h : Thesis.Tropical.Polynomial I, ∀ x, f x=g.eval x-h.eval x)
theorem _ThesisExactChecks.target_194 : _ThesisExpectedTypes.type_194 := by exact @Thesis.PiecewiseLinear.cpwl_polynomial_difference
end
run_cmd do
  let target ← getConstInfo `Thesis.PiecewiseLinear.cpwl_polynomial_difference
  let expected ← getConstInfo `_ThesisExactChecks.target_194
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.PiecewiseLinear.cpwl_polynomial_difference"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.PiecewiseLinear.cpwl_polynomial_difference | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.CPWLLattice do
    throwError "Defining module mismatch: Thesis.PiecewiseLinear.cpwl_polynomial_difference"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_194) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.PiecewiseLinear.cpwl_polynomial_difference: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.PiecewiseLinear.cpwl_polynomial_difference"
#check @Thesis.PiecewiseLinear.cpwl_polynomial_difference
#print axioms _ThesisExactChecks.target_194

section
open Set Filter Matrix Finset Thesis.Tropical Thesis.PiecewiseLinear
open scoped Topology
def _ThesisExpectedTypes.type_195 : Prop := (∀ {I : Type} [Fintype I] (f : (I → ℝ) → ℝ),
CPWL (fun x (_ : Unit) => f x) ↔
∃ g h : Thesis.Tropical.Polynomial I, ∀ x, f x=g.eval x-h.eval x)
theorem _ThesisExactChecks.target_195 : _ThesisExpectedTypes.type_195 := by exact @Thesis.PiecewiseLinear.cpwl_iff_polynomial_difference
end
run_cmd do
  let target ← getConstInfo `Thesis.PiecewiseLinear.cpwl_iff_polynomial_difference
  let expected ← getConstInfo `_ThesisExactChecks.target_195
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.PiecewiseLinear.cpwl_iff_polynomial_difference"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.PiecewiseLinear.cpwl_iff_polynomial_difference | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.CPWLLattice do
    throwError "Defining module mismatch: Thesis.PiecewiseLinear.cpwl_iff_polynomial_difference"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_195) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.PiecewiseLinear.cpwl_iff_polynomial_difference: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.PiecewiseLinear.cpwl_iff_polynomial_difference"
#check @Thesis.PiecewiseLinear.cpwl_iff_polynomial_difference
#print axioms _ThesisExactChecks.target_195

section
open Set Filter Matrix Finset HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis.ReLURepresentation
open scoped Topology
def _ThesisExpectedTypes.type_196 : Prop := (∀ {n : ℕ} (k : ℕ) (O : Type) [Fintype O]
(w : O → (Fin k → Bool) → Fin n → ℝ) (b : O → (Fin k → Bool) → ℝ),
∃ H : AffineHead n O, H.depth=k ∧
∀ x i, H.eval x i=finiteMax (fun t => w i t ⬝ᵥ x+b i t))
theorem _ThesisExactChecks.target_196 : _ThesisExpectedTypes.type_196 := by exact @Thesis.ReLURepresentation.affine_max_forest
end
run_cmd do
  let target ← getConstInfo `Thesis.ReLURepresentation.affine_max_forest
  let expected ← getConstInfo `_ThesisExactChecks.target_196
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ReLURepresentation.affine_max_forest"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReLURepresentation.affine_max_forest | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReLUCompiler do
    throwError "Defining module mismatch: Thesis.ReLURepresentation.affine_max_forest"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_196) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ReLURepresentation.affine_max_forest: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReLURepresentation.affine_max_forest"
#check @Thesis.ReLURepresentation.affine_max_forest
#print axioms _ThesisExactChecks.target_196

section
open Set Filter Matrix Finset HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis.ReLURepresentation
open scoped Topology
def _ThesisExpectedTypes.type_197 : Prop := (∀ {n k : ℕ} (O : Type) [Fintype O]
(p : O → Thesis.Tropical.Polynomial (Fin n))
(hcard : ∀ i, Fintype.card (p i).Terms≤2^k),
∃ H : AffineHead n O, H.depth=k ∧ ∀ x i, H.eval x i=(p i).eval x)
theorem _ThesisExactChecks.target_197 : _ThesisExpectedTypes.type_197 := by exact @Thesis.ReLURepresentation.polynomial_forest
end
run_cmd do
  let target ← getConstInfo `Thesis.ReLURepresentation.polynomial_forest
  let expected ← getConstInfo `_ThesisExactChecks.target_197
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ReLURepresentation.polynomial_forest"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReLURepresentation.polynomial_forest | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReLUCompiler do
    throwError "Defining module mismatch: Thesis.ReLURepresentation.polynomial_forest"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_197) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ReLURepresentation.polynomial_forest: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReLURepresentation.polynomial_forest"
#check @Thesis.ReLURepresentation.polynomial_forest
#print axioms _ThesisExactChecks.target_197

section
open Set Filter Matrix Finset HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis.ReLURepresentation
open scoped Topology
def _ThesisExpectedTypes.type_198 : Prop := (∀ {n k : ℕ} (O : Type) [Fintype O]
(p : O → Thesis.Tropical.Polynomial (Fin n)) (c : O → ℝ)
(hcard : ∀ i, Fintype.card (p i).Terms≤2^k),
∃ H : AffineHead n Unit, H.depth=k ∧
∀ x, H.eval x ()=∑ i, c i*(p i).eval x)
theorem _ThesisExactChecks.target_198 : _ThesisExpectedTypes.type_198 := by exact @Thesis.ReLURepresentation.signed_polynomial_compiler
end
run_cmd do
  let target ← getConstInfo `Thesis.ReLURepresentation.signed_polynomial_compiler
  let expected ← getConstInfo `_ThesisExactChecks.target_198
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ReLURepresentation.signed_polynomial_compiler"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReLURepresentation.signed_polynomial_compiler | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReLUCompiler do
    throwError "Defining module mismatch: Thesis.ReLURepresentation.signed_polynomial_compiler"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_198) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ReLURepresentation.signed_polynomial_compiler: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReLURepresentation.signed_polynomial_compiler"
#check @Thesis.ReLURepresentation.signed_polynomial_compiler
#print axioms _ThesisExactChecks.target_198

section
open Set Filter Matrix Finset HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis.ReLURepresentation
open scoped Topology
def _ThesisExpectedTypes.type_199 : Prop := (∀ {n : ℕ} (f : (Fin n → ℝ) → ℝ)
(hf : CPWL (fun x (_ : Unit) => f x)),
∃ (m : ℕ) (net : Network n m) (w : Fin m → ℝ) (b : ℝ),
hiddenDepth net+1≤⌈Real.logb 2 (n+1)⌉₊+1 ∧
∀ x, f x=w ⬝ᵥ net.eval x+b)
theorem _ThesisExactChecks.target_199 : _ThesisExpectedTypes.type_199 := by exact @Thesis.PiecewiseLinear.cpwl_relu_bounded_depth
end
run_cmd do
  let target ← getConstInfo `Thesis.PiecewiseLinear.cpwl_relu_bounded_depth
  let expected ← getConstInfo `_ThesisExactChecks.target_199
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.PiecewiseLinear.cpwl_relu_bounded_depth"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.PiecewiseLinear.cpwl_relu_bounded_depth | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.CPWLReLUEquivalence do
    throwError "Defining module mismatch: Thesis.PiecewiseLinear.cpwl_relu_bounded_depth"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_199) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.PiecewiseLinear.cpwl_relu_bounded_depth: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.PiecewiseLinear.cpwl_relu_bounded_depth"
#check @Thesis.PiecewiseLinear.cpwl_relu_bounded_depth
#print axioms _ThesisExactChecks.target_199

section
open Set Filter Matrix Finset HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis.ReLURepresentation
open scoped Topology
def _ThesisExpectedTypes.type_200 : Prop := (∀ {n : ℕ} (f : (Fin n → ℝ) → ℝ),
(CPWL (fun x (_ : Unit) => f x) ↔
  ∃ (m : ℕ) (net : Network n m) (w : Fin m → ℝ) (b : ℝ),
    ∀ x, f x=w ⬝ᵥ net.eval x+b) ∧
(CPWL (fun x (_ : Unit) => f x) →
  ∃ (m : ℕ) (net : Network n m) (w : Fin m → ℝ) (b : ℝ),
    hiddenDepth net+1≤⌈Real.logb 2 (n+1)⌉₊+1 ∧
    ∀ x, f x=w ⬝ᵥ net.eval x+b))
theorem _ThesisExactChecks.target_200 : _ThesisExpectedTypes.type_200 := by exact @Thesis.PiecewiseLinear.cpwl_relu_equivalence
end
run_cmd do
  let target ← getConstInfo `Thesis.PiecewiseLinear.cpwl_relu_equivalence
  let expected ← getConstInfo `_ThesisExactChecks.target_200
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.PiecewiseLinear.cpwl_relu_equivalence"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.PiecewiseLinear.cpwl_relu_equivalence | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.CPWLReLUEquivalence do
    throwError "Defining module mismatch: Thesis.PiecewiseLinear.cpwl_relu_equivalence"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_200) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.PiecewiseLinear.cpwl_relu_equivalence: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.PiecewiseLinear.cpwl_relu_equivalence"
#check @Thesis.PiecewiseLinear.cpwl_relu_equivalence
#print axioms _ThesisExactChecks.target_200

section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxIdentities
open scoped Classical
def _ThesisExpectedTypes.type_201 : Prop := (∀ {A : Type} [DecidableEq A] (f : A → ℝ) (B : Finset A) (hB : B.Nonempty)
    (a : A) (ha : f a ≤ B.sup' hB f) (S : Finset A),
    baseMax f B hB (insert a S) = baseMax f B hB S)
theorem _ThesisExactChecks.target_201 : _ThesisExpectedTypes.type_201 := by exact @Thesis.SignedMaxIdentities.baseMax_insert_dominated
end
run_cmd do
  let target ← getConstInfo `Thesis.SignedMaxIdentities.baseMax_insert_dominated
  let expected ← getConstInfo `_ThesisExactChecks.target_201
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SignedMaxIdentities.baseMax_insert_dominated"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SignedMaxIdentities.baseMax_insert_dominated | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SignedMaxIdentities do
    throwError "Defining module mismatch: Thesis.SignedMaxIdentities.baseMax_insert_dominated"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_201) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SignedMaxIdentities.baseMax_insert_dominated: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SignedMaxIdentities.baseMax_insert_dominated"
#check @Thesis.SignedMaxIdentities.baseMax_insert_dominated
#print axioms _ThesisExactChecks.target_201

section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxIdentities
open scoped Classical
def _ThesisExpectedTypes.type_202 : Prop := (∀ {A : Type} [DecidableEq A] (S : Finset A) (a : A) (ha : a ∈ S)
    (F : Finset A → ℝ)
    (hF : ∀ T ⊆ S.erase a, F (insert a T) = F T),
    (∑ T ∈ S.powerset, (-1 : ℝ)^T.card * F T) = 0)
theorem _ThesisExactChecks.target_202 : _ThesisExpectedTypes.type_202 := by exact @Thesis.SignedMaxIdentities.alternating_sum_zero_of_insertion
end
run_cmd do
  let target ← getConstInfo `Thesis.SignedMaxIdentities.alternating_sum_zero_of_insertion
  let expected ← getConstInfo `_ThesisExactChecks.target_202
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SignedMaxIdentities.alternating_sum_zero_of_insertion"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SignedMaxIdentities.alternating_sum_zero_of_insertion | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SignedMaxIdentities do
    throwError "Defining module mismatch: Thesis.SignedMaxIdentities.alternating_sum_zero_of_insertion"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_202) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SignedMaxIdentities.alternating_sum_zero_of_insertion: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SignedMaxIdentities.alternating_sum_zero_of_insertion"
#check @Thesis.SignedMaxIdentities.alternating_sum_zero_of_insertion
#print axioms _ThesisExactChecks.target_202

section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxIdentities
open scoped Classical
def _ThesisExpectedTypes.type_203 : Prop := (∀ {A : Type} [DecidableEq A] (f : A → ℝ) (A₀ B : Finset A) (hB : B.Nonempty)
    (hdom : ∃ a ∈ A₀, f a ≤ B.sup' hB f),
    (∑ S ∈ A₀.powerset, (-1 : ℝ)^S.card * baseMax f B hB S) = 0)
theorem _ThesisExactChecks.target_203 : _ThesisExpectedTypes.type_203 := by exact @Thesis.SignedMaxIdentities.alternating_max_zero
end
run_cmd do
  let target ← getConstInfo `Thesis.SignedMaxIdentities.alternating_max_zero
  let expected ← getConstInfo `_ThesisExactChecks.target_203
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SignedMaxIdentities.alternating_max_zero"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SignedMaxIdentities.alternating_max_zero | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SignedMaxIdentities do
    throwError "Defining module mismatch: Thesis.SignedMaxIdentities.alternating_max_zero"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_203) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SignedMaxIdentities.alternating_max_zero: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SignedMaxIdentities.alternating_max_zero"
#check @Thesis.SignedMaxIdentities.alternating_max_zero
#print axioms _ThesisExactChecks.target_203

section
open Finset Matrix Thesis.Tropical Thesis.AffineMaxPartition
open scoped Classical
def _ThesisExpectedTypes.type_204 : Prop := (∀ {I : Type} [Fintype I] (p : Polynomial I)
    (hcard : Fintype.card I + 1 < Fintype.card p.Terms),
    ∃ c : p.Terms → ℝ, (∑ i, c i) = 0 ∧ (∑ i, c i • p.slope i) = 0 ∧ ∃ i, c i ≠ 0)
theorem _ThesisExactChecks.target_204 : _ThesisExpectedTypes.type_204 := by exact @Thesis.AffineMaxPartition.dependence_coefficients
end
run_cmd do
  let target ← getConstInfo `Thesis.AffineMaxPartition.dependence_coefficients
  let expected ← getConstInfo `_ThesisExactChecks.target_204
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.AffineMaxPartition.dependence_coefficients"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AffineMaxPartition.dependence_coefficients | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AffineMaxPartition do
    throwError "Defining module mismatch: Thesis.AffineMaxPartition.dependence_coefficients"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_204) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AffineMaxPartition.dependence_coefficients: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AffineMaxPartition.dependence_coefficients"
#check @Thesis.AffineMaxPartition.dependence_coefficients
#print axioms _ThesisExactChecks.target_204

section
open Finset Matrix Thesis.Tropical Thesis.AffineMaxPartition
open scoped Classical
def _ThesisExpectedTypes.type_205 : Prop := (∀ {I : Type} [Fintype I] (p : Polynomial I)
    (hcard : Fintype.card I + 1 < Fintype.card p.Terms),
    ∃ c : p.Terms → ℝ, (∑ i, c i) = 0 ∧ (∑ i, c i • p.slope i) = 0 ∧
      (∑ i, c i * p.intercept i) ≤ 0 ∧ ∃ i, c i ≠ 0)
theorem _ThesisExactChecks.target_205 : _ThesisExpectedTypes.type_205 := by exact @Thesis.AffineMaxPartition.oriented_dependence
end
run_cmd do
  let target ← getConstInfo `Thesis.AffineMaxPartition.oriented_dependence
  let expected ← getConstInfo `_ThesisExactChecks.target_205
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.AffineMaxPartition.oriented_dependence"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AffineMaxPartition.oriented_dependence | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AffineMaxPartition do
    throwError "Defining module mismatch: Thesis.AffineMaxPartition.oriented_dependence"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_205) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AffineMaxPartition.oriented_dependence: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AffineMaxPartition.oriented_dependence"
#check @Thesis.AffineMaxPartition.oriented_dependence
#print axioms _ThesisExactChecks.target_205

section
open Finset Matrix Thesis.Tropical Thesis.AffineMaxPartition
open scoped Classical
def _ThesisExpectedTypes.type_206 : Prop := (∀ {I : Type} [Fintype I] (p : Polynomial I) (c : p.Terms → ℝ)
    (hv : (∑ i, c i • p.slope i) = 0) (x : I → ℝ),
    (∑ i, c i * (p.slope i ⬝ᵥ x + p.intercept i)) = ∑ i, c i * p.intercept i)
theorem _ThesisExactChecks.target_206 : _ThesisExpectedTypes.type_206 := by exact @Thesis.AffineMaxPartition.weighted_affine_constant
end
run_cmd do
  let target ← getConstInfo `Thesis.AffineMaxPartition.weighted_affine_constant
  let expected ← getConstInfo `_ThesisExactChecks.target_206
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.AffineMaxPartition.weighted_affine_constant"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AffineMaxPartition.weighted_affine_constant | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AffineMaxPartition do
    throwError "Defining module mismatch: Thesis.AffineMaxPartition.weighted_affine_constant"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_206) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AffineMaxPartition.weighted_affine_constant: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AffineMaxPartition.weighted_affine_constant"
#check @Thesis.AffineMaxPartition.weighted_affine_constant
#print axioms _ThesisExactChecks.target_206

section
open Finset Matrix Thesis.Tropical Thesis.AffineMaxPartition
open scoped Classical
def _ThesisExpectedTypes.type_207 : Prop := (∀ {I : Type} [Fintype I] (p : Polynomial I)
    (hcard : Fintype.card I + 1 < Fintype.card p.Terms),
    ∃ (A B : Finset p.Terms) (_ : A.Nonempty) (hB : B.Nonempty),
      Disjoint A B ∧ A ∪ B = Finset.univ ∧
      ∀ x : I → ℝ, ∃ a ∈ A,
        p.slope a ⬝ᵥ x + p.intercept a ≤ B.sup' hB (fun b => p.slope b ⬝ᵥ x + p.intercept b))
theorem _ThesisExactChecks.target_207 : _ThesisExpectedTypes.type_207 := by exact @Thesis.AffineMaxPartition.global_partition
end
run_cmd do
  let target ← getConstInfo `Thesis.AffineMaxPartition.global_partition
  let expected ← getConstInfo `_ThesisExactChecks.target_207
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.AffineMaxPartition.global_partition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AffineMaxPartition.global_partition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AffineMaxPartition do
    throwError "Defining module mismatch: Thesis.AffineMaxPartition.global_partition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_207) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AffineMaxPartition.global_partition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AffineMaxPartition.global_partition"
#check @Thesis.AffineMaxPartition.global_partition
#print axioms _ThesisExactChecks.target_207

section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxReduction
open scoped Classical
def _ThesisExpectedTypes.type_208 : Prop := (∀ {I : Type} (p : Polynomial I) (S : Finset p.Terms) (hS : S.Nonempty),
    Fintype.card (restrict p S hS).Terms = S.card)
theorem _ThesisExactChecks.target_208 : _ThesisExpectedTypes.type_208 := by exact @Thesis.SignedMaxReduction.restrict_card
end
run_cmd do
  let target ← getConstInfo `Thesis.SignedMaxReduction.restrict_card
  let expected ← getConstInfo `_ThesisExactChecks.target_208
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SignedMaxReduction.restrict_card"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SignedMaxReduction.restrict_card | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SignedMaxReduction do
    throwError "Defining module mismatch: Thesis.SignedMaxReduction.restrict_card"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_208) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SignedMaxReduction.restrict_card: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SignedMaxReduction.restrict_card"
#check @Thesis.SignedMaxReduction.restrict_card
#print axioms _ThesisExactChecks.target_208

section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxReduction
open scoped Classical
def _ThesisExpectedTypes.type_209 : Prop := (∀ {I : Type} [Fintype I] (p : Polynomial I) (S : Finset p.Terms) (hS : S.Nonempty)
    (x : I → ℝ),
    (restrict p S hS).eval x = S.sup' hS (fun a => p.slope a ⬝ᵥ x + p.intercept a))
theorem _ThesisExactChecks.target_209 : _ThesisExpectedTypes.type_209 := by exact @Thesis.SignedMaxReduction.restrict_eval
end
run_cmd do
  let target ← getConstInfo `Thesis.SignedMaxReduction.restrict_eval
  let expected ← getConstInfo `_ThesisExactChecks.target_209
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SignedMaxReduction.restrict_eval"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SignedMaxReduction.restrict_eval | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SignedMaxReduction do
    throwError "Defining module mismatch: Thesis.SignedMaxReduction.restrict_eval"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_209) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SignedMaxReduction.restrict_eval: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SignedMaxReduction.restrict_eval"
#check @Thesis.SignedMaxReduction.restrict_eval
#print axioms _ThesisExactChecks.target_209

section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxReduction
open scoped Classical
def _ThesisExpectedTypes.type_210 : Prop := (∀ {I : Type} [Fintype I] (p : Polynomial I),
    p.eval ∈ smallSpan I)
theorem _ThesisExactChecks.target_210 : _ThesisExpectedTypes.type_210 := by exact @Thesis.SignedMaxReduction.eval_mem_smallSpan
end
run_cmd do
  let target ← getConstInfo `Thesis.SignedMaxReduction.eval_mem_smallSpan
  let expected ← getConstInfo `_ThesisExactChecks.target_210
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SignedMaxReduction.eval_mem_smallSpan"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SignedMaxReduction.eval_mem_smallSpan | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SignedMaxReduction do
    throwError "Defining module mismatch: Thesis.SignedMaxReduction.eval_mem_smallSpan"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_210) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SignedMaxReduction.eval_mem_smallSpan: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SignedMaxReduction.eval_mem_smallSpan"
#check @Thesis.SignedMaxReduction.eval_mem_smallSpan
#print axioms _ThesisExactChecks.target_210

section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxReduction
open scoped Classical
def _ThesisExpectedTypes.type_211 : Prop := (∀ {I : Type} [Fintype I] (f : (I → ℝ) → ℝ)
    (hf : f ∈ smallSpan I),
    ∃ (N : ℕ) (c : Fin N → ℝ) (q : Fin N → Polynomial I),
      (∀ j, Fintype.card (q j).Terms ≤ Fintype.card I + 1) ∧
      ∀ x, f x = ∑ j, c j * (q j).eval x)
theorem _ThesisExactChecks.target_211 : _ThesisExpectedTypes.type_211 := by exact @Thesis.SignedMaxReduction.finite_representation_of_mem_smallSpan
end
run_cmd do
  let target ← getConstInfo `Thesis.SignedMaxReduction.finite_representation_of_mem_smallSpan
  let expected ← getConstInfo `_ThesisExactChecks.target_211
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SignedMaxReduction.finite_representation_of_mem_smallSpan"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SignedMaxReduction.finite_representation_of_mem_smallSpan | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SignedMaxReduction do
    throwError "Defining module mismatch: Thesis.SignedMaxReduction.finite_representation_of_mem_smallSpan"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_211) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SignedMaxReduction.finite_representation_of_mem_smallSpan: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SignedMaxReduction.finite_representation_of_mem_smallSpan"
#check @Thesis.SignedMaxReduction.finite_representation_of_mem_smallSpan
#print axioms _ThesisExactChecks.target_211

section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxReduction
open scoped Classical
def _ThesisExpectedTypes.type_212 : Prop := (∀ {I : Type} [Fintype I] (p : Polynomial I),
    ∃ (N : ℕ) (c : Fin N → ℝ) (q : Fin N → Polynomial I),
      (∀ j, Fintype.card (q j).Terms ≤ Fintype.card I + 1) ∧
      ∀ x, p.eval x = ∑ j, c j * (q j).eval x)
theorem _ThesisExactChecks.target_212 : _ThesisExpectedTypes.type_212 := by exact @Thesis.SignedMaxReduction.polynomial_signed_small_max
end
run_cmd do
  let target ← getConstInfo `Thesis.SignedMaxReduction.polynomial_signed_small_max
  let expected ← getConstInfo `_ThesisExactChecks.target_212
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SignedMaxReduction.polynomial_signed_small_max"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SignedMaxReduction.polynomial_signed_small_max | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SignedMaxReduction do
    throwError "Defining module mismatch: Thesis.SignedMaxReduction.polynomial_signed_small_max"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_212) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SignedMaxReduction.polynomial_signed_small_max: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SignedMaxReduction.polynomial_signed_small_max"
#check @Thesis.SignedMaxReduction.polynomial_signed_small_max
#print axioms _ThesisExactChecks.target_212

section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxReduction
open scoped Classical
def _ThesisExpectedTypes.type_213 : Prop := (∀ {I : Type} [Fintype I] (p r : Polynomial I),
    ∃ (N : ℕ) (c : Fin N → ℝ) (q : Fin N → Polynomial I),
      (∀ j, Fintype.card (q j).Terms ≤ Fintype.card I + 1) ∧
      ∀ x, p.eval x - r.eval x = ∑ j, c j * (q j).eval x)
theorem _ThesisExactChecks.target_213 : _ThesisExpectedTypes.type_213 := by exact @Thesis.SignedMaxReduction.difference_signed_small_max
end
run_cmd do
  let target ← getConstInfo `Thesis.SignedMaxReduction.difference_signed_small_max
  let expected ← getConstInfo `_ThesisExactChecks.target_213
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SignedMaxReduction.difference_signed_small_max"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SignedMaxReduction.difference_signed_small_max | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SignedMaxReduction do
    throwError "Defining module mismatch: Thesis.SignedMaxReduction.difference_signed_small_max"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_213) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SignedMaxReduction.difference_signed_small_max: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SignedMaxReduction.difference_signed_small_max"
#check @Thesis.SignedMaxReduction.difference_signed_small_max
#print axioms _ThesisExactChecks.target_213

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_214 : Prop := (∀ (R : Regularizer) (z : ℝ), ∃ p ∈ Icc (0 : ℝ) 1, IsMaxOn (objective R z) (Icc 0 1) p)
theorem _ThesisExactChecks.target_214 : _ThesisExpectedTypes.type_214 := by exact @Thesis.GeneralRegularization.exists_optimizer
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.exists_optimizer
  let expected ← getConstInfo `_ThesisExactChecks.target_214
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.exists_optimizer"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.exists_optimizer | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.exists_optimizer"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_214) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.exists_optimizer: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.exists_optimizer"
#check @Thesis.GeneralRegularization.exists_optimizer
#print axioms _ThesisExactChecks.target_214

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_215 : Prop := (∀ (R : Regularizer) (z : ℝ), IsGreatest ((objective R z) '' Icc (0 : ℝ) 1) (activation R z))
theorem _ThesisExactChecks.target_215 : _ThesisExpectedTypes.type_215 := by exact @Thesis.GeneralRegularization.activation_isGreatest
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.activation_isGreatest
  let expected ← getConstInfo `_ThesisExactChecks.target_215
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.activation_isGreatest"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.activation_isGreatest | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.activation_isGreatest"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_215) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.activation_isGreatest: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.activation_isGreatest"
#check @Thesis.GeneralRegularization.activation_isGreatest
#print axioms _ThesisExactChecks.target_215

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_216 : Prop := (∀ (R : Regularizer) (π : ℝ → ℝ)
(hπ : ∀ z, π z ∈ Icc (0 : ℝ) 1 ∧ IsMaxOn (objective R z) (Icc 0 1) (π z))
{n m k : ℕ} (net : Network n m) (x : PairVec n)
(wp wn : Matrix (Fin k) (Fin m) ℝ) (bp bn : Vec k),
ValidPairActivation (activation R) (pairWith R π) ∧
NonnegativePairActivation (pairWith R π) ∧
ConvexOn ℝ univ (activation R) ∧ Monotone (activation R) ∧
LipschitzWith 1 (activation R) ∧
(∀ z, DifferentiableAt ℝ (activation R) z → π z = deriv (activation R) z) ∧
(preP wp wn (net.decomposeWith (pairWith R π) x)+bp -
(preN wp wn (net.decomposeWith (pairWith R π) x)+bn) =
affineLayer wp wn bp bn (net.forwardWith (activation R) (x.1-x.2))))
theorem _ThesisExactChecks.target_216 : _ThesisExpectedTypes.type_216 := by exact @Thesis.GeneralRegularization.regularized_decomposition_validity
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.regularized_decomposition_validity
  let expected ← getConstInfo `_ThesisExactChecks.target_216
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.regularized_decomposition_validity"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.regularized_decomposition_validity | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.regularized_decomposition_validity"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_216) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.regularized_decomposition_validity: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.regularized_decomposition_validity"
#check @Thesis.GeneralRegularization.regularized_decomposition_validity
#print axioms _ThesisExactChecks.target_216

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_217 : Prop := (∀ z : ℝ, activation zeroRegularizer z = relu z)
theorem _ThesisExactChecks.target_217 : _ThesisExpectedTypes.type_217 := by exact @Thesis.GeneralRegularization.zero_activation
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.zero_activation
  let expected ← getConstInfo `_ThesisExactChecks.target_217
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.zero_activation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.zero_activation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.zero_activation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_217) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.zero_activation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.zero_activation"
#check @Thesis.GeneralRegularization.zero_activation
#print axioms _ThesisExactChecks.target_217

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_218 : Prop := (pairWith zeroRegularizer hardGate = Thesis.StoppingDecomposition.stopPair)
theorem _ThesisExactChecks.target_218 : _ThesisExpectedTypes.type_218 := by exact @Thesis.GeneralRegularization.zero_pair_is_stopping
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.zero_pair_is_stopping
  let expected ← getConstInfo `_ThesisExactChecks.target_218
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.zero_pair_is_stopping"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.zero_pair_is_stopping | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.zero_pair_is_stopping"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_218) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.zero_pair_is_stopping: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.zero_pair_is_stopping"
#check @Thesis.GeneralRegularization.zero_pair_is_stopping
#print axioms _ThesisExactChecks.target_218

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_219 : Prop := (∀ (θ : ℝ) (hθ : 0 < θ) (z : ℝ),
Thesis.Regularization.gate θ z ∈ Icc (0 : ℝ) 1 ∧
IsMaxOn (objective (entropyRegularizer θ hθ) z) (Icc 0 1)
  (Thesis.Regularization.gate θ z))
theorem _ThesisExactChecks.target_219 : _ThesisExpectedTypes.type_219 := by exact @Thesis.GeneralRegularization.sigmoid_optimal
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.sigmoid_optimal
  let expected ← getConstInfo `_ThesisExactChecks.target_219
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.sigmoid_optimal"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.sigmoid_optimal | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.sigmoid_optimal"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_219) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.sigmoid_optimal: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.sigmoid_optimal"
#check @Thesis.GeneralRegularization.sigmoid_optimal
#print axioms _ThesisExactChecks.target_219

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_220 : Prop := (∀ (θ : ℝ) (hθ : 0 < θ) (z : ℝ), activation (entropyRegularizer θ hθ) z = Thesis.Regularization.softplus θ z)
theorem _ThesisExactChecks.target_220 : _ThesisExpectedTypes.type_220 := by exact @Thesis.GeneralRegularization.entropy_activation
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.entropy_activation
  let expected ← getConstInfo `_ThesisExactChecks.target_220
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.entropy_activation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.entropy_activation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.entropy_activation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_220) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.entropy_activation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.entropy_activation"
#check @Thesis.GeneralRegularization.entropy_activation
#print axioms _ThesisExactChecks.target_220

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_221 : Prop := (∀ (θ : ℝ) (hθ : 0 < θ) (z : ℝ × ℝ),
pairWith (entropyRegularizer θ hθ) (Thesis.Regularization.gate θ) z =
Thesis.Regularization.softSplit θ z.1 z.2)
theorem _ThesisExactChecks.target_221 : _ThesisExpectedTypes.type_221 := by exact @Thesis.GeneralRegularization.entropy_pair_is_softSplit
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.entropy_pair_is_softSplit
  let expected ← getConstInfo `_ThesisExactChecks.target_221
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.entropy_pair_is_softSplit"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.entropy_pair_is_softSplit | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.entropy_pair_is_softSplit"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_221) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.entropy_pair_is_softSplit: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.entropy_pair_is_softSplit"
#check @Thesis.GeneralRegularization.entropy_pair_is_softSplit
#print axioms _ThesisExactChecks.target_221

section
open Set HiddenMonotonicity
def _ThesisExpectedTypes.type_222 : Prop := (∀ {d n m : ℕ} (net : Network n m) (hw : net.Nonnegative)
(p q : Vec d → Vec n)
(hp : ∀ i, ConvexOn ℝ univ (fun x => p x i))
(hq : ∀ i, ConvexOn ℝ univ (fun x => q x i)),
(∀ i, ConvexOn ℝ univ (fun x => (net.split (p x) (q x)).1 i)) ∧
(∀ i, ConvexOn ℝ univ (fun x => (net.split (p x) (q x)).2 i)))
theorem _ThesisExactChecks.target_222 : _ThesisExpectedTypes.type_222 := by exact @HiddenMonotonicity.Network.split_convex_input
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.split_convex_input
  let expected ← getConstInfo `_ThesisExactChecks.target_222
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.split_convex_input"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.split_convex_input | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexInput do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.split_convex_input"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_222) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.split_convex_input: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.split_convex_input"
#check @HiddenMonotonicity.Network.split_convex_input
#print axioms _ThesisExactChecks.target_222

section
open Set HiddenMonotonicity
def _ThesisExpectedTypes.type_223 : Prop := (∀ {d n m : ℕ} (net : Network n m) (hw : net.Nonnegative)
(p q : Vec d → Vec n)
(hp : ∀ i, ConvexOn ℝ univ (fun x => p x i))
(hq : ∀ i, ConvexOn ℝ univ (fun x => q x i))
(wp wn : Vec m) (hwp : ∀ i, 0 ≤ wp i) (hwn : ∀ i, 0 ≤ wn i) (bp bn : ℝ),
ConvexOn ℝ univ (fun x => (net.affineHeads (coefficientRow wp) (coefficientRow wn) bp bn (p x,q x)).1) ∧
ConvexOn ℝ univ (fun x => (net.affineHeads (coefficientRow wp) (coefficientRow wn) bp bn (p x,q x)).2))
theorem _ThesisExactChecks.target_223 : _ThesisExpectedTypes.type_223 := by exact @HiddenMonotonicity.Network.affine_heads_convex_input
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_heads_convex_input
  let expected ← getConstInfo `_ThesisExactChecks.target_223
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_heads_convex_input"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_heads_convex_input | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexInput do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_heads_convex_input"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_223) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_heads_convex_input: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_heads_convex_input"
#check @HiddenMonotonicity.Network.affine_heads_convex_input
#print axioms _ThesisExactChecks.target_223

section
open Set HiddenMonotonicity
def _ThesisExpectedTypes.type_224 : Prop := (∀ {d n m : ℕ} (net : Network n m) (hw : net.Nonnegative)
(p q : Vec d → Vec n)
(hp : ∀ i, ConvexOn ℝ univ (fun x => p x i))
(hq : ∀ i, ConvexOn ℝ univ (fun x => q x i)),
(∀ i, ConvexOn ℝ univ (fun x => (net.decomposeWith (mixPair 1) (p x,q x)).1 i)) ∧
(∀ i, ConvexOn ℝ univ (fun x => (net.decomposeWith (mixPair 1) (p x,q x)).2 i)) ∧
(∀ x, (net.decomposeWith (mixPair 1) (p x,q x)).1 - (net.decomposeWith (mixPair 1) (p x,q x)).2 = net.eval (p x-q x)))
theorem _ThesisExactChecks.target_224 : _ThesisExpectedTypes.type_224 := by exact @HiddenMonotonicity.Network.mixing_one_convex_input
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.mixing_one_convex_input
  let expected ← getConstInfo `_ThesisExactChecks.target_224
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.mixing_one_convex_input"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.mixing_one_convex_input | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexInput do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.mixing_one_convex_input"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_224) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.mixing_one_convex_input: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.mixing_one_convex_input"
#check @HiddenMonotonicity.Network.mixing_one_convex_input
#print axioms _ThesisExactChecks.target_224

section
open HiddenMonotonicity HiddenMonotonicity.Convolution
def _ThesisExpectedTypes.type_225 : Prop := (∀ {ci co ip op taps : ℕ}
(K : Fin co → Fin ci → Fin taps → ℝ)
(stencil : Fin op → Fin taps → Option (Fin ip)) (x : Vec (ci*ip)),
applyKernel K stencil x = (kernelMatrix K stencil).mulVec x)
theorem _ThesisExactChecks.target_225 : _ThesisExpectedTypes.type_225 := by exact @HiddenMonotonicity.Convolution.applyKernel_eq_mulVec
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Convolution.applyKernel_eq_mulVec
  let expected ← getConstInfo `_ThesisExactChecks.target_225
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Convolution.applyKernel_eq_mulVec"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Convolution.applyKernel_eq_mulVec | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Convolution do
    throwError "Defining module mismatch: HiddenMonotonicity.Convolution.applyKernel_eq_mulVec"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_225) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Convolution.applyKernel_eq_mulVec: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Convolution.applyKernel_eq_mulVec"
#check @HiddenMonotonicity.Convolution.applyKernel_eq_mulVec
#print axioms _ThesisExactChecks.target_225

section
open HiddenMonotonicity HiddenMonotonicity.Convolution
def _ThesisExpectedTypes.type_226 : Prop := (∀ {ci co ip op taps : ℕ}
(K : Fin co → Fin ci → Fin taps → ℝ)
(stencil : Fin op → Fin taps → Option (Fin ip)) (x : Vec (ci*ip)),
HasFDerivAt (applyKernel K stencil) (matrixCLM (kernelMatrix K stencil)) x)
theorem _ThesisExactChecks.target_226 : _ThesisExpectedTypes.type_226 := by exact @HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt
  let expected ← getConstInfo `_ThesisExactChecks.target_226
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Convolution do
    throwError "Defining module mismatch: HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_226) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt"
#check @HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt
#print axioms _ThesisExactChecks.target_226

section
open HiddenMonotonicity HiddenMonotonicity.Convolution
def _ThesisExpectedTypes.type_227 : Prop := (∀ {ci co ip op taps : ℕ}
(K : Fin co → Fin ci → Fin taps → ℝ)
(stencil : Fin op → Fin taps → Option (Fin ip)) (b : Fin co → ℝ) (x : PairVec (ci*ip)),
HasFDerivAt (splitKernel K stencil b)
((preP (kernelMatrix (positiveKernel K) stencil) (kernelMatrix (negativeKernel K) stencil)).prod
(preN (kernelMatrix (positiveKernel K) stencil) (kernelMatrix (negativeKernel K) stencil))) x)
theorem _ThesisExactChecks.target_227 : _ThesisExpectedTypes.type_227 := by exact @HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt
  let expected ← getConstInfo `_ThesisExactChecks.target_227
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Convolution do
    throwError "Defining module mismatch: HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_227) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt"
#check @HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt
#print axioms _ThesisExactChecks.target_227

section
open HiddenMonotonicity HiddenMonotonicity.Convolution
def _ThesisExpectedTypes.type_228 : Prop := (∀ {ci co ip op taps : ℕ}
(K : Fin co → Fin ci → Fin taps → ℝ)
(stencil : Fin op → Fin taps → Option (Fin ip)) (b : Fin co → ℝ),
(∀ x, 0 ≤ x → 0 ≤ splitKernel K stencil b x) ∧
Monotone (splitKernel K stencil b) ∧
(∀ i, ConvexOn ℝ Set.univ (fun x => (splitKernel K stencil b x).1 i) ∧
ConvexOn ℝ Set.univ (fun x => (splitKernel K stencil b x).2 i)) ∧
(∀ x, (splitKernel K stencil b x).1-(splitKernel K stencil b x).2 =
applyKernel K stencil (x.1-x.2)+(fun u => b (unflat u).1)))
theorem _ThesisExactChecks.target_228 : _ThesisExpectedTypes.type_228 := by exact @HiddenMonotonicity.Convolution.splitKernel_properties
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Convolution.splitKernel_properties
  let expected ← getConstInfo `_ThesisExactChecks.target_228
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Convolution.splitKernel_properties"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Convolution.splitKernel_properties | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Convolution do
    throwError "Defining module mismatch: HiddenMonotonicity.Convolution.splitKernel_properties"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_228) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Convolution.splitKernel_properties: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Convolution.splitKernel_properties"
#check @HiddenMonotonicity.Convolution.splitKernel_properties
#print axioms _ThesisExactChecks.target_228

section
open HiddenMonotonicity Finset Matrix
def _ThesisExpectedTypes.type_229 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (x : Fin d × Bool → ℝ),
c.compileSplitDAG.eval x=c.split false x)
theorem _ThesisExactChecks.target_229 : _ThesisExpectedTypes.type_229 := by exact @HiddenMonotonicity.Circuit.compileSplitDAG_eval
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Circuit.compileSplitDAG_eval
  let expected ← getConstInfo `_ThesisExactChecks.target_229
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Circuit.compileSplitDAG_eval"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Circuit.compileSplitDAG_eval | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SplitDAGSize do
    throwError "Defining module mismatch: HiddenMonotonicity.Circuit.compileSplitDAG_eval"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_229) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Circuit.compileSplitDAG_eval: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Circuit.compileSplitDAG_eval"
#check @HiddenMonotonicity.Circuit.compileSplitDAG_eval
#print axioms _ThesisExactChecks.target_229

section
open HiddenMonotonicity Finset Matrix
def _ThesisExpectedTypes.type_230 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (D : ℕ)
(hc : c.BoundedDuplication D),
c.compileSplitDAG.graphSize≤24*2^D*c.syntaxSize ∧
(∀ x : Fin d × Bool → ℝ,
  (c.compileSplitDAG.eval x).1-(c.compileSplitDAG.eval x).2=
    c.eval (fun i => x (i,false)-x (i,true))) ∧
(∀ x : Fin d × Bool → ℝ, 0≤x → 0≤c.compileSplitDAG.eval x) ∧
(∀ x y : Fin d × Bool → ℝ, 0≤x → 0≤y → x≤y →
  c.compileSplitDAG.eval x≤c.compileSplitDAG.eval y))
theorem _ThesisExactChecks.target_230 : _ThesisExpectedTypes.type_230 := by exact @HiddenMonotonicity.Circuit.split_DAG_with_size
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Circuit.split_DAG_with_size
  let expected ← getConstInfo `_ThesisExactChecks.target_230
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Circuit.split_DAG_with_size"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Circuit.split_DAG_with_size | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SplitDAGSize do
    throwError "Defining module mismatch: HiddenMonotonicity.Circuit.split_DAG_with_size"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_230) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Circuit.split_DAG_with_size: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Circuit.split_DAG_with_size"
#check @HiddenMonotonicity.Circuit.split_DAG_with_size
#print axioms _ThesisExactChecks.target_230

section
open HiddenMonotonicity Finset Matrix
def _ThesisExpectedTypes.type_231 : Prop := (∀ {n : ℕ} (g : MaxoutProductGate n) (x : Vec n),
g.toExpr.eval x=g.eval x)
theorem _ThesisExactChecks.target_231 : _ThesisExpectedTypes.type_231 := by exact @HiddenMonotonicity.MaxoutProductGate.toExpr_eval
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaxoutProductGate.toExpr_eval
  let expected ← getConstInfo `_ThesisExactChecks.target_231
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaxoutProductGate.toExpr_eval"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaxoutProductGate.toExpr_eval | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MaxoutProductSize do
    throwError "Defining module mismatch: HiddenMonotonicity.MaxoutProductGate.toExpr_eval"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_231) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaxoutProductGate.toExpr_eval: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaxoutProductGate.toExpr_eval"
#check @HiddenMonotonicity.MaxoutProductGate.toExpr_eval
#print axioms _ThesisExactChecks.target_231

section
open HiddenMonotonicity Finset Matrix
def _ThesisExpectedTypes.type_232 : Prop := (∀ {d n : ℕ} (c : MaxoutProductDAG d n) (x : Vec d),
c.toCircuit.eval x=c.eval x)
theorem _ThesisExactChecks.target_232 : _ThesisExpectedTypes.type_232 := by exact @HiddenMonotonicity.MaxoutProductDAG.toCircuit_eval
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaxoutProductDAG.toCircuit_eval
  let expected ← getConstInfo `_ThesisExactChecks.target_232
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaxoutProductDAG.toCircuit_eval"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaxoutProductDAG.toCircuit_eval | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MaxoutProductSize do
    throwError "Defining module mismatch: HiddenMonotonicity.MaxoutProductDAG.toCircuit_eval"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_232) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaxoutProductDAG.toCircuit_eval: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaxoutProductDAG.toCircuit_eval"
#check @HiddenMonotonicity.MaxoutProductDAG.toCircuit_eval
#print axioms _ThesisExactChecks.target_232

section
open HiddenMonotonicity Finset Matrix
def _ThesisExpectedTypes.type_233 : Prop := (∀ {d n : ℕ} (c : MaxoutProductDAG d n) (x : Vec d),
c.eval x=(c.compile.eval (canonicalSplitInput x)).1-
(c.compile.eval (canonicalSplitInput x)).2)
theorem _ThesisExactChecks.target_233 : _ThesisExpectedTypes.type_233 := by exact @HiddenMonotonicity.MaxoutProductDAG.compile_canonical_recovery
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaxoutProductDAG.compile_canonical_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_233
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaxoutProductDAG.compile_canonical_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaxoutProductDAG.compile_canonical_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MaxoutProductSize do
    throwError "Defining module mismatch: HiddenMonotonicity.MaxoutProductDAG.compile_canonical_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_233) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaxoutProductDAG.compile_canonical_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaxoutProductDAG.compile_canonical_recovery"
#check @HiddenMonotonicity.MaxoutProductDAG.compile_canonical_recovery
#print axioms _ThesisExactChecks.target_233

section
open HiddenMonotonicity Finset Matrix
def _ThesisExpectedTypes.type_234 : Prop := (∀ {d n : ℕ} (c : MaxoutProductDAG d n) (K D : ℕ)
(hc : c.BoundedRankDegree K D),
∃ g : SplitDAG d n,
g.maxoutRank≤2 ∧ g.graphSize≤(24*2^(max K D)*(4*K+2*D+1))*c.graphSize ∧
(∀ x : Fin d × Bool → ℝ, (g.eval x).1-(g.eval x).2=
  c.eval (fun i => x (i,false)-x (i,true))) ∧
(∀ x : Fin d × Bool → ℝ, 0≤x → 0≤g.eval x) ∧
(∀ x y : Fin d × Bool → ℝ, 0≤x → 0≤y → x≤y → g.eval x≤g.eval y) ∧
(∀ i : Fin n, ∃ P Q : MaxPolynomial (Fin d × Bool),
  ∀ x : Fin d × Bool → ℝ, 0≤x → (g.eval x).1 i=P.eval x ∧ (g.eval x).2 i=Q.eval x))
theorem _ThesisExactChecks.target_234 : _ThesisExpectedTypes.type_234 := by exact @HiddenMonotonicity.MaxoutProductDAG.split_linear_size
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaxoutProductDAG.split_linear_size
  let expected ← getConstInfo `_ThesisExactChecks.target_234
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaxoutProductDAG.split_linear_size"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaxoutProductDAG.split_linear_size | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MaxoutProductSize do
    throwError "Defining module mismatch: HiddenMonotonicity.MaxoutProductDAG.split_linear_size"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_234) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaxoutProductDAG.split_linear_size: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaxoutProductDAG.split_linear_size"
#check @HiddenMonotonicity.MaxoutProductDAG.split_linear_size
#print axioms _ThesisExactChecks.target_234

section
open HiddenMonotonicity Finset Matrix
def _ThesisExpectedTypes.type_235 : Prop := (∀ {n : ℕ} (g : MaxoutProductGate n),
g.totalDegree≤g.expandedTerms)
theorem _ThesisExactChecks.target_235 : _ThesisExpectedTypes.type_235 := by exact @HiddenMonotonicity.MaxoutProductGate.degree_le_expandedTerms
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaxoutProductGate.degree_le_expandedTerms
  let expected ← getConstInfo `_ThesisExactChecks.target_235
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaxoutProductGate.degree_le_expandedTerms"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaxoutProductGate.degree_le_expandedTerms | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MaxoutProductSize do
    throwError "Defining module mismatch: HiddenMonotonicity.MaxoutProductGate.degree_le_expandedTerms"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_235) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaxoutProductGate.degree_le_expandedTerms: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaxoutProductGate.degree_le_expandedTerms"
#check @HiddenMonotonicity.MaxoutProductGate.degree_le_expandedTerms
#print axioms _ThesisExactChecks.target_235

section
open HiddenMonotonicity Finset Matrix
def _ThesisExpectedTypes.type_236 : Prop := (∀ {d n : ℕ} (c : MaxoutProductDAG d n) (K B : ℕ)
(hc : c.BoundedRankExpansion K B),
∃ g : SplitDAG d n,
g.maxoutRank≤2 ∧ g.graphSize≤(24*2^(max K B)*(4*K+2*B+1))*c.graphSize ∧
(∀ x : Fin d × Bool → ℝ, (g.eval x).1-(g.eval x).2=
  c.eval (fun i => x (i,false)-x (i,true))) ∧
(∀ x : Fin d × Bool → ℝ, 0≤x → 0≤g.eval x) ∧
(∀ x y : Fin d × Bool → ℝ, 0≤x → 0≤y → x≤y → g.eval x≤g.eval y) ∧
(∀ i : Fin n, ∃ P Q : MaxPolynomial (Fin d × Bool),
  ∀ x : Fin d × Bool → ℝ, 0≤x → (g.eval x).1 i=P.eval x ∧ (g.eval x).2 i=Q.eval x))
theorem _ThesisExactChecks.target_236 : _ThesisExpectedTypes.type_236 := by exact @HiddenMonotonicity.MaxoutProductDAG.split_linear_size_expansion
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaxoutProductDAG.split_linear_size_expansion
  let expected ← getConstInfo `_ThesisExactChecks.target_236
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaxoutProductDAG.split_linear_size_expansion"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaxoutProductDAG.split_linear_size_expansion | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MaxoutProductSize do
    throwError "Defining module mismatch: HiddenMonotonicity.MaxoutProductDAG.split_linear_size_expansion"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_236) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaxoutProductDAG.split_linear_size_expansion: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaxoutProductDAG.split_linear_size_expansion"
#check @HiddenMonotonicity.MaxoutProductDAG.split_linear_size_expansion
#print axioms _ThesisExactChecks.target_236

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_237 : Prop := (∀ {n : ℕ} (e : SignedExpr (Fin n)) (he : e.Additive) (x : PairVec n) (hx : ExpressionRegular e x), HasFDerivAt (stoppingExpr e) (kernelMap (expressionKernel e x)) x)
theorem _ThesisExactChecks.target_237 : _ThesisExpectedTypes.type_237 := by exact @Thesis.StoppingDAG.stoppingExpr_hasFDerivAt
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.stoppingExpr_hasFDerivAt
  let expected ← getConstInfo `_ThesisExactChecks.target_237
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.stoppingExpr_hasFDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.stoppingExpr_hasFDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingExpressionKernel do
    throwError "Defining module mismatch: Thesis.StoppingDAG.stoppingExpr_hasFDerivAt"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_237) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.stoppingExpr_hasFDerivAt: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.stoppingExpr_hasFDerivAt"
#check @Thesis.StoppingDAG.stoppingExpr_hasFDerivAt
#print axioms _ThesisExactChecks.target_237

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_238 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (hx : CircuitRegular c x), HasFDerivAt (stoppingCircuit c) (pairMap (dagKernel c x).1 (dagKernel c x).2) x)
theorem _ThesisExactChecks.target_238 : _ThesisExpectedTypes.type_238 := by exact @Thesis.StoppingDAG.stoppingCircuit_hasFDerivAt
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.stoppingCircuit_hasFDerivAt
  let expected ← getConstInfo `_ThesisExactChecks.target_238
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.stoppingCircuit_hasFDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.stoppingCircuit_hasFDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGDerivative do
    throwError "Defining module mismatch: Thesis.StoppingDAG.stoppingCircuit_hasFDerivAt"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_238) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.stoppingCircuit_hasFDerivAt: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.stoppingCircuit_hasFDerivAt"
#check @Thesis.StoppingDAG.stoppingCircuit_hasFDerivAt
#print axioms _ThesisExactChecks.target_238

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_239 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (j : Fin n) (path : DAGPaths c), 0≤pathProbability c x j path)
theorem _ThesisExactChecks.target_239 : _ThesisExpectedTypes.type_239 := by exact @Thesis.StoppingDAG.pathProbability_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.pathProbability_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_239
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.pathProbability_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.pathProbability_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPaths do
    throwError "Defining module mismatch: Thesis.StoppingDAG.pathProbability_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_239) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.pathProbability_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.pathProbability_nonnegative"
#check @Thesis.StoppingDAG.pathProbability_nonnegative
#print axioms _ThesisExactChecks.target_239

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_240 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (x : PairVec d) (j : Fin n), (∑ path : DAGPaths c,pathProbability c x j path)=1)
theorem _ThesisExactChecks.target_240 : _ThesisExpectedTypes.type_240 := by exact @Thesis.StoppingDAG.pathProbability_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.pathProbability_normalized
  let expected ← getConstInfo `_ThesisExactChecks.target_240
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.pathProbability_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.pathProbability_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPaths do
    throwError "Defining module mismatch: Thesis.StoppingDAG.pathProbability_normalized"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_240) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.pathProbability_normalized: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.pathProbability_normalized"
#check @Thesis.StoppingDAG.pathProbability_normalized
#print axioms _ThesisExactChecks.target_240

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_241 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (j : Fin n) (path : DAGPaths c), 0≤pathDiscount c x j path)
theorem _ThesisExactChecks.target_241 : _ThesisExpectedTypes.type_241 := by exact @Thesis.StoppingDAG.pathDiscount_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.pathDiscount_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_241
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.pathDiscount_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.pathDiscount_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPaths do
    throwError "Defining module mismatch: Thesis.StoppingDAG.pathDiscount_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_241) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.pathDiscount_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.pathDiscount_nonnegative"
#check @Thesis.StoppingDAG.pathDiscount_nonnegative
#print axioms _ThesisExactChecks.target_241

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_242 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool), occupation c x j turn i channel = if Bool.xor channel turn then (dagKernel c x).2 j i else (dagKernel c x).1 j i)
theorem _ThesisExactChecks.target_242 : _ThesisExpectedTypes.type_242 := by exact @Thesis.StoppingDAG.occupation_eq_kernel
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.occupation_eq_kernel
  let expected ← getConstInfo `_ThesisExactChecks.target_242
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.occupation_eq_kernel"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.occupation_eq_kernel | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGOccupation do
    throwError "Defining module mismatch: Thesis.StoppingDAG.occupation_eq_kernel"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_242) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.occupation_eq_kernel: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.occupation_eq_kernel"
#check @Thesis.StoppingDAG.occupation_eq_kernel
#print axioms _ThesisExactChecks.target_242

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_243 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool), (if turn then (pairMap (dagKernel c x).1 (dagKernel c x).2 (splitBasis i channel)).2 j else (pairMap (dagKernel c x).1 (dagKernel c x).2 (splitBasis i channel)).1 j) = occupation c x j turn i channel)
theorem _ThesisExactChecks.target_243 : _ThesisExpectedTypes.type_243 := by exact @Thesis.StoppingDAG.selected_operator_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.selected_operator_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_243
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.selected_operator_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.selected_operator_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGBackward do
    throwError "Defining module mismatch: Thesis.StoppingDAG.selected_operator_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_243) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.selected_operator_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.selected_operator_occupation"
#check @Thesis.StoppingDAG.selected_operator_occupation
#print axioms _ThesisExactChecks.target_243

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_244 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (hx : CircuitRegular c x) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool), (if turn then (fderiv ℝ (stoppingCircuit c) x (splitBasis i channel)).2 j else (fderiv ℝ (stoppingCircuit c) x (splitBasis i channel)).1 j) = occupation c x j turn i channel)
theorem _ThesisExactChecks.target_244 : _ThesisExpectedTypes.type_244 := by exact @Thesis.StoppingDAG.stopping_derivative_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.stopping_derivative_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_244
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.stopping_derivative_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.stopping_derivative_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGBackward do
    throwError "Defining module mismatch: Thesis.StoppingDAG.stopping_derivative_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_244) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.stopping_derivative_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.stopping_derivative_occupation"
#check @Thesis.StoppingDAG.stopping_derivative_occupation
#print axioms _ThesisExactChecks.target_244

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_245 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : Vec d) (hx : CircuitRegular c (x,0)), HasFDerivAt c.eval (matrixCLM ((dagKernel c (x,0)).1-(dagKernel c (x,0)).2)) x)
theorem _ThesisExactChecks.target_245 : _ThesisExpectedTypes.type_245 := by exact @Thesis.StoppingDAG.circuit_hasFDerivAt
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.circuit_hasFDerivAt
  let expected ← getConstInfo `_ThesisExactChecks.target_245
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.circuit_hasFDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.circuit_hasFDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGBackward do
    throwError "Defining module mismatch: Thesis.StoppingDAG.circuit_hasFDerivAt"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_245) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.circuit_hasFDerivAt: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.circuit_hasFDerivAt"
#check @Thesis.StoppingDAG.circuit_hasFDerivAt
#print axioms _ThesisExactChecks.target_245

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_246 : Prop := (∀ {n : ℕ} (e : SignedExpr (Fin n)) (he : e.Additive) (x : PairVec n), stoppingExpr e x=kernelMap (expressionKernel e x) x+expressionOffset e x)
theorem _ThesisExactChecks.target_246 : _ThesisExpectedTypes.type_246 := by exact @Thesis.StoppingDAG.stoppingExpr_affine
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.stoppingExpr_affine
  let expected ← getConstInfo `_ThesisExactChecks.target_246
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.stoppingExpr_affine"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.stoppingExpr_affine | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPayoff do
    throwError "Defining module mismatch: Thesis.StoppingDAG.stoppingExpr_affine"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_246) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.stoppingExpr_affine: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.stoppingExpr_affine"
#check @Thesis.StoppingDAG.stoppingExpr_affine
#print axioms _ThesisExactChecks.target_246

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_247 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (j : Fin n) (turn : Bool), expectedPayoff c x j turn=streamValue (stoppingCircuit c x) j turn)
theorem _ThesisExactChecks.target_247 : _ThesisExpectedTypes.type_247 := by exact @Thesis.StoppingDAG.expectedPayoff_eq_stoppingCircuit
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.expectedPayoff_eq_stoppingCircuit
  let expected ← getConstInfo `_ThesisExactChecks.target_247
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.expectedPayoff_eq_stoppingCircuit"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.expectedPayoff_eq_stoppingCircuit | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPayoff do
    throwError "Defining module mismatch: Thesis.StoppingDAG.expectedPayoff_eq_stoppingCircuit"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_247) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.expectedPayoff_eq_stoppingCircuit: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.expectedPayoff_eq_stoppingCircuit"
#check @Thesis.StoppingDAG.expectedPayoff_eq_stoppingCircuit
#print axioms _ThesisExactChecks.target_247

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_248 : Prop := (∀ {n : ℕ} (w : Vec n) (b : ℝ) (x : PairVec n), expressionKernel (SignedExpr.affine w b) x=(fun i => max (w i) 0,fun i => max (-w i) 0))
theorem _ThesisExactChecks.target_248 : _ThesisExpectedTypes.type_248 := by exact @Thesis.StoppingDAG.expressionKernel_affine
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.expressionKernel_affine
  let expected ← getConstInfo `_ThesisExactChecks.target_248
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.expressionKernel_affine"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.expressionKernel_affine | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPrimitives do
    throwError "Defining module mismatch: Thesis.StoppingDAG.expressionKernel_affine"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_248) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.expressionKernel_affine: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.expressionKernel_affine"
#check @Thesis.StoppingDAG.expressionKernel_affine
#print axioms _ThesisExactChecks.target_248

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_249 : Prop := (∀ {n : ℕ} (w : Vec n) (b : ℝ) (x : PairVec n), expressionOffset (SignedExpr.affine w b) x=(max b 0,max (-b) 0))
theorem _ThesisExactChecks.target_249 : _ThesisExpectedTypes.type_249 := by exact @Thesis.StoppingDAG.expressionOffset_affine
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.expressionOffset_affine
  let expected ← getConstInfo `_ThesisExactChecks.target_249
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.expressionOffset_affine"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.expressionOffset_affine | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPrimitives do
    throwError "Defining module mismatch: Thesis.StoppingDAG.expressionOffset_affine"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_249) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.expressionOffset_affine: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.expressionOffset_affine"
#check @Thesis.StoppingDAG.expressionOffset_affine
#print axioms _ThesisExactChecks.target_249

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_250 : Prop := (∀ {n : ℕ} (w : Vec n) (b : ℝ) (x : PairVec n), localDiscount (expressionKernel (SignedExpr.affine w b) x)=∑ i,|w i|)
theorem _ThesisExactChecks.target_250 : _ThesisExpectedTypes.type_250 := by exact @Thesis.StoppingDAG.affine_discount
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.affine_discount
  let expected ← getConstInfo `_ThesisExactChecks.target_250
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.affine_discount"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.affine_discount | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPrimitives do
    throwError "Defining module mismatch: Thesis.StoppingDAG.affine_discount"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_250) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.affine_discount: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.affine_discount"
#check @Thesis.StoppingDAG.affine_discount
#print axioms _ThesisExactChecks.target_250

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_251 : Prop := (∀ {n : ℕ} (b : ℝ) (x : PairVec n), localDiscount (expressionKernel (.constant b) x)=0 ∧ localProbability (expressionKernel (.constant b) x) none=1 ∧ expressionOffset (.constant b) x=(max b 0,max (-b) 0))
theorem _ThesisExactChecks.target_251 : _ThesisExpectedTypes.type_251 := by exact @Thesis.StoppingDAG.constant_cemetery
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.constant_cemetery
  let expected ← getConstInfo `_ThesisExactChecks.target_251
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.constant_cemetery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.constant_cemetery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPrimitives do
    throwError "Defining module mismatch: Thesis.StoppingDAG.constant_cemetery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_251) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.constant_cemetery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.constant_cemetery"
#check @Thesis.StoppingDAG.constant_cemetery
#print axioms _ThesisExactChecks.target_251

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_252 : Prop := (∀ {n : ℕ} (i j : Fin n) (x : PairVec n), localDiscount (expressionKernel (.add (.input i) (.input j)) x)=2)
theorem _ThesisExactChecks.target_252 : _ThesisExpectedTypes.type_252 := by exact @Thesis.StoppingDAG.addition_discount
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.addition_discount
  let expected ← getConstInfo `_ThesisExactChecks.target_252
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.addition_discount"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.addition_discount | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPrimitives do
    throwError "Defining module mismatch: Thesis.StoppingDAG.addition_discount"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_252) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.addition_discount: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.addition_discount"
#check @Thesis.StoppingDAG.addition_discount
#print axioms _ThesisExactChecks.target_252

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_253 : Prop := (∀ {n : ℕ} (i j k : Fin n) (x : PairVec n), localProbability (expressionKernel (.add (.input i) (.input j)) x) (some (k,false)) = additionProbability false*(if k=i then 1 else 0)+additionProbability true*(if k=j then 1 else 0))
theorem _ThesisExactChecks.target_253 : _ThesisExpectedTypes.type_253 := by exact @Thesis.StoppingDAG.addition_probability
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.addition_probability
  let expected ← getConstInfo `_ThesisExactChecks.target_253
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.addition_probability"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.addition_probability | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPrimitives do
    throwError "Defining module mismatch: Thesis.StoppingDAG.addition_probability"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_253) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.addition_probability: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.addition_probability"
#check @Thesis.StoppingDAG.addition_probability
#print axioms _ThesisExactChecks.target_253

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_254 : Prop := (∀ {n : ℕ} (i j : Fin n) (x : PairVec n), expressionKernel (.maximum (.input i) (.input j)) x = (Pi.single (if x.1 j-x.2 j<x.1 i-x.2 i then i else j) 1,0))
theorem _ThesisExactChecks.target_254 : _ThesisExpectedTypes.type_254 := by exact @Thesis.StoppingDAG.pool_kernel
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.pool_kernel
  let expected ← getConstInfo `_ThesisExactChecks.target_254
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.pool_kernel"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.pool_kernel | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPrimitives do
    throwError "Defining module mismatch: Thesis.StoppingDAG.pool_kernel"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_254) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.pool_kernel: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.pool_kernel"
#check @Thesis.StoppingDAG.pool_kernel
#print axioms _ThesisExactChecks.target_254

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_255 : Prop := (∀ {n : ℕ} (i j : Fin n) (x : PairVec n), localDiscount (expressionKernel (.maximum (.input i) (.input j)) x)=1)
theorem _ThesisExactChecks.target_255 : _ThesisExpectedTypes.type_255 := by exact @Thesis.StoppingDAG.pool_discount
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.pool_discount
  let expected ← getConstInfo `_ThesisExactChecks.target_255
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.pool_discount"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.pool_discount | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPrimitives do
    throwError "Defining module mismatch: Thesis.StoppingDAG.pool_discount"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_255) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.pool_discount: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.pool_discount"
#check @Thesis.StoppingDAG.pool_discount
#print axioms _ThesisExactChecks.target_255

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_256 : Prop := (∀ {n : ℕ} (i : Fin n) (x : PairVec n), expressionKernel (.maximum (.input i) (.constant 0)) x = if x.2 i<x.1 i then (Pi.single i 1,0) else (0,0))
theorem _ThesisExactChecks.target_256 : _ThesisExpectedTypes.type_256 := by exact @Thesis.StoppingDAG.relu_kernel
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.relu_kernel
  let expected ← getConstInfo `_ThesisExactChecks.target_256
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.relu_kernel"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.relu_kernel | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPrimitives do
    throwError "Defining module mismatch: Thesis.StoppingDAG.relu_kernel"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_256) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.relu_kernel: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.relu_kernel"
#check @Thesis.StoppingDAG.relu_kernel
#print axioms _ThesisExactChecks.target_256

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_257 : Prop := (∀ {d m n : ℕ} (pre : Circuit d m) (suffix : Circuit m n) (x : PairVec d), stoppingCircuit (graft pre suffix) x=stoppingCircuit suffix (stoppingCircuit pre x))
theorem _ThesisExactChecks.target_257 : _ThesisExpectedTypes.type_257 := by exact @Thesis.StoppingDAG.graft_stopping
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.graft_stopping
  let expected ← getConstInfo `_ThesisExactChecks.target_257
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.graft_stopping"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.graft_stopping | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGCuts do
    throwError "Defining module mismatch: Thesis.StoppingDAG.graft_stopping"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_257) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.graft_stopping: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.graft_stopping"
#check @Thesis.StoppingDAG.graft_stopping
#print axioms _ThesisExactChecks.target_257

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_258 : Prop := (∀ {d m n : ℕ} (pre : Circuit d (m+1)) (suffix : Circuit (m+1) n) (hc : (graft pre suffix).Additive) (x : PairVec d) (j : Fin n) (turn channel : Bool), fullOccupation (graft pre suffix) x j turn m channel = occupation suffix (stoppingCircuit pre x) j turn (Fin.last m) channel)
theorem _ThesisExactChecks.target_258 : _ThesisExpectedTypes.type_258 := by exact @Thesis.StoppingDAG.fullOccupation_graft_last
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.fullOccupation_graft_last
  let expected ← getConstInfo `_ThesisExactChecks.target_258
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.fullOccupation_graft_last"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.fullOccupation_graft_last | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGVisits do
    throwError "Defining module mismatch: Thesis.StoppingDAG.fullOccupation_graft_last"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_258) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.fullOccupation_graft_last: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.fullOccupation_graft_last"
#check @Thesis.StoppingDAG.fullOccupation_graft_last
#print axioms _ThesisExactChecks.target_258

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_259 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (s : PairVec d) (hs : CircuitRegular c s), HasFDerivAt c.eval (matrixCLM ((dagKernel c s).1-(dagKernel c s).2)) (s.1-s.2))
theorem _ThesisExactChecks.target_259 : _ThesisExpectedTypes.type_259 := by exact @Thesis.StoppingDAG.circuit_hasFDerivAt_split
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.circuit_hasFDerivAt_split
  let expected ← getConstInfo `_ThesisExactChecks.target_259
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.circuit_hasFDerivAt_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.circuit_hasFDerivAt_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGIntermediate do
    throwError "Defining module mismatch: Thesis.StoppingDAG.circuit_hasFDerivAt_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_259) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.circuit_hasFDerivAt_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.circuit_hasFDerivAt_split"
#check @Thesis.StoppingDAG.circuit_hasFDerivAt_split
#print axioms _ThesisExactChecks.target_259

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_260 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (target : ℕ) (hd : d≤target) (hn : target<n), ∃ pre : Circuit d (target+1),∃ suffix : Circuit (target+1) n,c=graft pre suffix)
theorem _ThesisExactChecks.target_260 : _ThesisExpectedTypes.type_260 := by exact @Thesis.StoppingDAG.exists_graph_cut
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.exists_graph_cut
  let expected ← getConstInfo `_ThesisExactChecks.target_260
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.exists_graph_cut"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.exists_graph_cut | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGIntermediate do
    throwError "Defining module mismatch: Thesis.StoppingDAG.exists_graph_cut"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_260) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.exists_graph_cut: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.exists_graph_cut"
#check @Thesis.StoppingDAG.exists_graph_cut
#print axioms _ThesisExactChecks.target_260

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_261 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool), fullOccupation c x j turn i.val channel=occupation c x j turn i channel)
theorem _ThesisExactChecks.target_261 : _ThesisExpectedTypes.type_261 := by exact @Thesis.StoppingDAG.fullOccupation_input
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.fullOccupation_input
  let expected ← getConstInfo `_ThesisExactChecks.target_261
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.fullOccupation_input"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.fullOccupation_input | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGIntermediate do
    throwError "Defining module mismatch: Thesis.StoppingDAG.fullOccupation_input"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_261) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.fullOccupation_input: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.fullOccupation_input"
#check @Thesis.StoppingDAG.fullOccupation_input
#print axioms _ThesisExactChecks.target_261

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_262 : Prop := (∀ {d m n : ℕ} (pre : Circuit d (m+1)) (suffix : Circuit (m+1) n) (hc : (graft pre suffix).Additive) (x : PairVec d) (hx : CircuitRegular (graft pre suffix) x) (j : Fin n) (p q k : Bool), (if Bool.xor p q then (fderiv ℝ (stoppingCircuit suffix) (stoppingCircuit pre x) (splitBasis (Fin.last m) k)).2 j else (fderiv ℝ (stoppingCircuit suffix) (stoppingCircuit pre x) (splitBasis (Fin.last m) k)).1 j) = fullOccupation (graft pre suffix) x j q m (Bool.xor p k))
theorem _ThesisExactChecks.target_262 : _ThesisExpectedTypes.type_262 := by exact @Thesis.StoppingDAG.intermediate_stopping_derivative_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.intermediate_stopping_derivative_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_262
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.intermediate_stopping_derivative_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.intermediate_stopping_derivative_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGIntermediate do
    throwError "Defining module mismatch: Thesis.StoppingDAG.intermediate_stopping_derivative_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_262) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.intermediate_stopping_derivative_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.intermediate_stopping_derivative_occupation"
#check @Thesis.StoppingDAG.intermediate_stopping_derivative_occupation
#print axioms _ThesisExactChecks.target_262

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_263 : Prop := (∀ {d m n : ℕ} (pre : Circuit d (m+1)) (suffix : Circuit (m+1) n) (hc : (graft pre suffix).Additive) (x : PairVec d) (hx : CircuitRegular (graft pre suffix) x) (j : Fin n) (q : Bool), (fderiv ℝ suffix.eval (pre.eval (x.1-x.2)) (Pi.single (Fin.last m) 1)) j = (if q then (-1 : ℝ) else 1)*(fullOccupation (graft pre suffix) x j q m false-fullOccupation (graft pre suffix) x j q m true))
theorem _ThesisExactChecks.target_263 : _ThesisExpectedTypes.type_263 := by exact @Thesis.StoppingDAG.intermediate_circuit_derivative_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.intermediate_circuit_derivative_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_263
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.intermediate_circuit_derivative_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.intermediate_circuit_derivative_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGIntermediate do
    throwError "Defining module mismatch: Thesis.StoppingDAG.intermediate_circuit_derivative_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_263) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.intermediate_circuit_derivative_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.intermediate_circuit_derivative_occupation"
#check @Thesis.StoppingDAG.intermediate_circuit_derivative_occupation
#print axioms _ThesisExactChecks.target_263

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
def _ThesisExpectedTypes.type_264 : Prop := (∀ {d m n : ℕ} (pre : Circuit d (m+1)) (suffix : Circuit (m+1) n) (hc : (graft pre suffix).Additive) (x : PairVec d) (j : Fin n) (p q k : Bool), (if Bool.xor p q then (pairMap (dagKernel suffix (stoppingCircuit pre x)).1 (dagKernel suffix (stoppingCircuit pre x)).2 (splitBasis (Fin.last m) k)).2 j else (pairMap (dagKernel suffix (stoppingCircuit pre x)).1 (dagKernel suffix (stoppingCircuit pre x)).2 (splitBasis (Fin.last m) k)).1 j) = fullOccupation (graft pre suffix) x j q m (Bool.xor p k))
theorem _ThesisExactChecks.target_264 : _ThesisExpectedTypes.type_264 := by exact @Thesis.StoppingDAG.intermediate_selected_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.intermediate_selected_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_264
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.intermediate_selected_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.intermediate_selected_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGIntermediate do
    throwError "Defining module mismatch: Thesis.StoppingDAG.intermediate_selected_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_264) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.intermediate_selected_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.intermediate_selected_occupation"
#check @Thesis.StoppingDAG.intermediate_selected_occupation
#print axioms _ThesisExactChecks.target_264

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDAG
open scoped BigOperators
def _ThesisExpectedTypes.type_265 : Prop := (∀ {k : ℕ} (v : Fin (k+1) → ℝ), (∀ i,v i ≤ v (earliestWinner v)) ∧ (∀ i,v i=v (earliestWinner v) → earliestWinner v ≤ i))
theorem _ThesisExactChecks.target_265 : _ThesisExpectedTypes.type_265 := by exact @Thesis.StoppingDAG.earliestWinner_spec
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.earliestWinner_spec
  let expected ← getConstInfo `_ThesisExactChecks.target_265
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.earliestWinner_spec"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.earliestWinner_spec | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingOrderedPool do
    throwError "Defining module mismatch: Thesis.StoppingDAG.earliestWinner_spec"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_265) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.earliestWinner_spec: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.earliestWinner_spec"
#check @Thesis.StoppingDAG.earliestWinner_spec
#print axioms _ThesisExactChecks.target_265

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDAG
open scoped BigOperators
def _ThesisExpectedTypes.type_266 : Prop := (∀ {n k : ℕ} (inputs : Fin (k+1) → Fin n) (x : PairVec n), let values := fun i => x.1 (inputs i)-x.2 (inputs i); let winner := earliestWinner values; (∀ i,values i ≤ values winner) ∧ (∀ i,values i=values winner → winner ≤ i) ∧ stoppingExpr (orderedInputPool inputs) x=(x.1 (inputs winner),x.2 (inputs winner)) ∧ expressionKernel (orderedInputPool inputs) x=(Pi.single (inputs winner) 1,0))
theorem _ThesisExactChecks.target_266 : _ThesisExpectedTypes.type_266 := by exact @Thesis.StoppingDAG.orderedInputPool_source
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.orderedInputPool_source
  let expected ← getConstInfo `_ThesisExactChecks.target_266
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.orderedInputPool_source"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.orderedInputPool_source | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingOrderedPool do
    throwError "Defining module mismatch: Thesis.StoppingDAG.orderedInputPool_source"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_266) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.orderedInputPool_source: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.orderedInputPool_source"
#check @Thesis.StoppingDAG.orderedInputPool_source
#print axioms _ThesisExactChecks.target_266

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDAG
open scoped BigOperators
def _ThesisExpectedTypes.type_267 : Prop := (∀ {n k : ℕ} (inputs : Fin (k+1) → Fin n) (horder : Monotone inputs) (x : PairVec n), let values := fun i => x.1 (inputs i)-x.2 (inputs i); let winner := earliestWinner values; ∀ i,values i=values winner → inputs winner ≤ inputs i)
theorem _ThesisExactChecks.target_267 : _ThesisExpectedTypes.type_267 := by exact @Thesis.StoppingDAG.orderedInputPool_minimum_graph_index
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.orderedInputPool_minimum_graph_index
  let expected ← getConstInfo `_ThesisExactChecks.target_267
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.orderedInputPool_minimum_graph_index"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.orderedInputPool_minimum_graph_index | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingOrderedPool do
    throwError "Defining module mismatch: Thesis.StoppingDAG.orderedInputPool_minimum_graph_index"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_267) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.orderedInputPool_minimum_graph_index: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.orderedInputPool_minimum_graph_index"
#check @Thesis.StoppingDAG.orderedInputPool_minimum_graph_index
#print axioms _ThesisExactChecks.target_267

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDAG
open scoped BigOperators
def _ThesisExpectedTypes.type_268 : Prop := (∀ {d n k : ℕ} (prior : Circuit d n) (inputs : Fin (k+1) → Fin n) (x : PairVec d), let s := stoppingCircuit prior x; let winner := earliestWinner (fun i => s.1 (inputs i)-s.2 (inputs i)); (dagKernel (.node prior (orderedInputPool inputs)) x).1 (Fin.last n)=(dagKernel prior x).1 (inputs winner) ∧ (dagKernel (.node prior (orderedInputPool inputs)) x).2 (Fin.last n)=(dagKernel prior x).2 (inputs winner))
theorem _ThesisExactChecks.target_268 : _ThesisExpectedTypes.type_268 := by exact @Thesis.StoppingDAG.orderedInputPool_dag_row
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.orderedInputPool_dag_row
  let expected ← getConstInfo `_ThesisExactChecks.target_268
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.orderedInputPool_dag_row"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.orderedInputPool_dag_row | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingOrderedPool do
    throwError "Defining module mismatch: Thesis.StoppingDAG.orderedInputPool_dag_row"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_268) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.orderedInputPool_dag_row: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.orderedInputPool_dag_row"
#check @Thesis.StoppingDAG.orderedInputPool_dag_row
#print axioms _ThesisExactChecks.target_268

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDAG
open scoped BigOperators
def _ThesisExpectedTypes.type_269 : Prop := (∀ {n k : ℕ} (es : Fin (k+1) → SignedExpr (Fin n)) (x : PairVec n) (winner : Fin (k+1)) (hw : ∀ i,i≠winner → score (es i) x<score (es winner) x) (hr : ExpressionRegular (es winner) x), ExpressionRegular (orderedPool es) x)
theorem _ThesisExactChecks.target_269 : _ThesisExpectedTypes.type_269 := by exact @Thesis.StoppingDAG.orderedPool_regular
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.orderedPool_regular
  let expected ← getConstInfo `_ThesisExactChecks.target_269
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.orderedPool_regular"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.orderedPool_regular | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingOrderedPool do
    throwError "Defining module mismatch: Thesis.StoppingDAG.orderedPool_regular"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_269) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.orderedPool_regular: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.orderedPool_regular"
#check @Thesis.StoppingDAG.orderedPool_regular
#print axioms _ThesisExactChecks.target_269

section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDAG
open scoped BigOperators
def _ThesisExpectedTypes.type_270 : Prop := (∀ {n k : ℕ} (inputs : Fin (k+1) → Fin n) (x : PairVec n) (winner : Fin (k+1)) (hw : ∀ i,i≠winner → x.1 (inputs i)-x.2 (inputs i)<x.1 (inputs winner)-x.2 (inputs winner)), ExpressionRegular (orderedInputPool inputs) x)
theorem _ThesisExactChecks.target_270 : _ThesisExpectedTypes.type_270 := by exact @Thesis.StoppingDAG.orderedInputPool_regular
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.orderedInputPool_regular
  let expected ← getConstInfo `_ThesisExactChecks.target_270
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.orderedInputPool_regular"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.orderedInputPool_regular | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingOrderedPool do
    throwError "Defining module mismatch: Thesis.StoppingDAG.orderedInputPool_regular"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_270) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.orderedInputPool_regular: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.orderedInputPool_regular"
#check @Thesis.StoppingDAG.orderedInputPool_regular
#print axioms _ThesisExactChecks.target_270

section
open Filter Thesis.Regularization
open scoped Topology
def _ThesisExpectedTypes.type_271 : Prop := (∀ (z : ℝ) (hz : 0 < z), Tendsto (fun θ : ℝ => gate θ z) (𝓝[>] 0) (𝓝 1))
theorem _ThesisExactChecks.target_271 : _ThesisExpectedTypes.type_271 := by exact @Thesis.SoftplusLimits.gate_limit_positive
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusLimits.gate_limit_positive
  let expected ← getConstInfo `_ThesisExactChecks.target_271
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusLimits.gate_limit_positive"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusLimits.gate_limit_positive | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusLimits do
    throwError "Defining module mismatch: Thesis.SoftplusLimits.gate_limit_positive"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_271) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusLimits.gate_limit_positive: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusLimits.gate_limit_positive"
#check @Thesis.SoftplusLimits.gate_limit_positive
#print axioms _ThesisExactChecks.target_271

section
open Filter Thesis.Regularization
open scoped Topology
def _ThesisExpectedTypes.type_272 : Prop := (∀ (z : ℝ) (hz : z < 0), Tendsto (fun θ : ℝ => gate θ z) (𝓝[>] 0) (𝓝 0))
theorem _ThesisExactChecks.target_272 : _ThesisExpectedTypes.type_272 := by exact @Thesis.SoftplusLimits.gate_limit_negative
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusLimits.gate_limit_negative
  let expected ← getConstInfo `_ThesisExactChecks.target_272
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusLimits.gate_limit_negative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusLimits.gate_limit_negative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusLimits do
    throwError "Defining module mismatch: Thesis.SoftplusLimits.gate_limit_negative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_272) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusLimits.gate_limit_negative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusLimits.gate_limit_negative"
#check @Thesis.SoftplusLimits.gate_limit_negative
#print axioms _ThesisExactChecks.target_272

section
open Filter Thesis.Regularization
open scoped Topology
def _ThesisExpectedTypes.type_273 : Prop := (∀ (u v : ℝ) (hne : u ≠ v), Tendsto (fun θ : ℝ => softSplit θ u v) (𝓝[>] 0) (𝓝 (Thesis.StoppingDecomposition.stopPair (u,v))))
theorem _ThesisExactChecks.target_273 : _ThesisExpectedTypes.type_273 := by exact @Thesis.SoftplusLimits.softSplit_tendsto_stopping
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusLimits.softSplit_tendsto_stopping
  let expected ← getConstInfo `_ThesisExactChecks.target_273
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusLimits.softSplit_tendsto_stopping"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusLimits.softSplit_tendsto_stopping | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusLimits do
    throwError "Defining module mismatch: Thesis.SoftplusLimits.softSplit_tendsto_stopping"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_273) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusLimits.softSplit_tendsto_stopping: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusLimits.softSplit_tendsto_stopping"
#check @Thesis.SoftplusLimits.softSplit_tendsto_stopping
#print axioms _ThesisExactChecks.target_273

section
open Filter Thesis.Regularization
open scoped Topology
def _ThesisExpectedTypes.type_274 : Prop := (∀ u : ℝ, Tendsto (fun θ : ℝ => softSplit θ u u) (𝓝[>] 0) (𝓝 (u/2,u/2)))
theorem _ThesisExactChecks.target_274 : _ThesisExpectedTypes.type_274 := by exact @Thesis.SoftplusLimits.softSplit_tendsto_tie
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusLimits.softSplit_tendsto_tie
  let expected ← getConstInfo `_ThesisExactChecks.target_274
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusLimits.softSplit_tendsto_tie"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusLimits.softSplit_tendsto_tie | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusLimits do
    throwError "Defining module mismatch: Thesis.SoftplusLimits.softSplit_tendsto_tie"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_274) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusLimits.softSplit_tendsto_tie: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusLimits.softSplit_tendsto_tie"
#check @Thesis.SoftplusLimits.softSplit_tendsto_tie
#print axioms _ThesisExactChecks.target_274

section
open Thesis.StoppingCircuit
def _ThesisExpectedTypes.type_275 : Prop := (∀ (left right : ℝ), 2*(additionProbability false*left+additionProbability true*right)=left+right)
theorem _ThesisExactChecks.target_275 : _ThesisExpectedTypes.type_275 := by exact @Thesis.StoppingCircuit.addition_discounted_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingCircuit.addition_discounted_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_275
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingCircuit.addition_discounted_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingCircuit.addition_discounted_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingCircuit do
    throwError "Defining module mismatch: Thesis.StoppingCircuit.addition_discounted_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_275) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingCircuit.addition_discounted_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingCircuit.addition_discounted_occupation"
#check @Thesis.StoppingCircuit.addition_discounted_occupation
#print axioms _ThesisExactChecks.target_275

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_276 : Prop := (∀ {n k : ℕ} (r : Set.Icc (0 : ℝ) 1) (wp wn : Matrix (Fin k) (Fin n) ℝ) (j : Fin k) (turn : Bool), (∑ target,mixedTransition r wp wn j turn target)=1)
theorem _ThesisExactChecks.target_276 : _ThesisExpectedTypes.type_276 := by exact @Thesis.SoftplusGame.mixedTransition_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.mixedTransition_normalized
  let expected ← getConstInfo `_ThesisExactChecks.target_276
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.mixedTransition_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.mixedTransition_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusPolicies do
    throwError "Defining module mismatch: Thesis.SoftplusGame.mixedTransition_normalized"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_276) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.mixedTransition_normalized: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.mixedTransition_normalized"
#check @Thesis.SoftplusGame.mixedTransition_normalized
#print axioms _ThesisExactChecks.target_276

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_277 : Prop := (∀ {n k : ℕ} (r : Set.Icc (0 : ℝ) 1) (wp wn : Matrix (Fin k) (Fin n) ℝ) (hw : ∀ j i,0≤wp j i ∧ 0≤wn j i) (j : Fin k) (turn : Bool) (target : Option (Fin n × Bool)), 0≤mixedTransition r wp wn j turn target)
theorem _ThesisExactChecks.target_277 : _ThesisExpectedTypes.type_277 := by exact @Thesis.SoftplusGame.mixedTransition_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.mixedTransition_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_277
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.mixedTransition_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.mixedTransition_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusPolicies do
    throwError "Defining module mismatch: Thesis.SoftplusGame.mixedTransition_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_277) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.mixedTransition_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.mixedTransition_nonnegative"
#check @Thesis.SoftplusGame.mixedTransition_nonnegative
#print axioms _ThesisExactChecks.target_277

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_278 : Prop := (∀ {n k : ℕ} (r : Set.Icc (0 : ℝ) 1) (wp wn : Matrix (Fin k) (Fin n) ℝ) (j : Fin k) (turn : Bool) (hz : fanIn wp wn j=0), mixedTransition r wp wn j turn none=1)
theorem _ThesisExactChecks.target_278 : _ThesisExpectedTypes.type_278 := by exact @Thesis.SoftplusGame.mixed_zero_fanIn_absorbs
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.mixed_zero_fanIn_absorbs
  let expected ← getConstInfo `_ThesisExactChecks.target_278
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.mixed_zero_fanIn_absorbs"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.mixed_zero_fanIn_absorbs | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusPolicies do
    throwError "Defining module mismatch: Thesis.SoftplusGame.mixed_zero_fanIn_absorbs"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_278) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.mixed_zero_fanIn_absorbs: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.mixed_zero_fanIn_absorbs"
#check @Thesis.SoftplusGame.mixed_zero_fanIn_absorbs
#print axioms _ThesisExactChecks.target_278

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_279 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (hw : ∀ j i,0≤wp j i ∧ 0≤wn j i) (b : Vec k) (p q : Vec n) (j : Fin k), continuation wp wn b p q j=((wp *ᵥ p+wn *ᵥ q)+b) j)
theorem _ThesisExactChecks.target_279 : _ThesisExpectedTypes.type_279 := by exact @Thesis.SoftplusGame.continuation_recovery_total
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.continuation_recovery_total
  let expected ← getConstInfo `_ThesisExactChecks.target_279
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.continuation_recovery_total"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.continuation_recovery_total | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusPolicies do
    throwError "Defining module mismatch: Thesis.SoftplusGame.continuation_recovery_total"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_279) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.continuation_recovery_total: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.continuation_recovery_total"
#check @Thesis.SoftplusGame.continuation_recovery_total
#print axioms _ThesisExactChecks.target_279

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_280 : Prop := (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net),
 (policyValue θ net plus (gibbsStrategy θ net x) x (-x)).1≤softEval θ net x ∧
 (policyValue θ net plus (gibbsStrategy θ net x) x (-x)).2≤ -softEval θ net x ∧
 policyValue θ net (gibbsStrategy θ net x) (gibbsStrategy θ net x) x (-x)=(softEval θ net x,-softEval θ net x) ∧
 softEval θ net x≤(policyValue θ net (gibbsStrategy θ net x) minus x (-x)).1 ∧
 -softEval θ net x≤(policyValue θ net (gibbsStrategy θ net x) minus x (-x)).2)
theorem _ThesisExactChecks.target_280 : _ThesisExpectedTypes.type_280 := by exact @Thesis.SoftplusGame.softplus_saddle
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.softplus_saddle
  let expected ← getConstInfo `_ThesisExactChecks.target_280
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.softplus_saddle"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.softplus_saddle | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusEquilibrium do
    throwError "Defining module mismatch: Thesis.SoftplusGame.softplus_saddle"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_280) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.softplus_saddle: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.softplus_saddle"
#check @Thesis.SoftplusGame.softplus_saddle
#print axioms _ThesisExactChecks.target_280

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_281 : Prop := (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net), SubgamePerfect θ net plus minus x (-x) ↔ plus=gibbsStrategy θ net x ∧ minus=gibbsStrategy θ net x)
theorem _ThesisExactChecks.target_281 : _ThesisExpectedTypes.type_281 := by exact @Thesis.SoftplusGame.subgamePerfect_iff
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.subgamePerfect_iff
  let expected ← getConstInfo `_ThesisExactChecks.target_281
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.subgamePerfect_iff"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.subgamePerfect_iff | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusEquilibrium do
    throwError "Defining module mismatch: Thesis.SoftplusGame.subgamePerfect_iff"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_281) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.subgamePerfect_iff: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.subgamePerfect_iff"
#check @Thesis.SoftplusGame.subgamePerfect_iff
#print axioms _ThesisExactChecks.target_281

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_282 : Prop := (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (hw : net.Nonnegative) (plus minus : Strategy net) (v : PlayerValues n), advantage (playerValue θ net plus minus v)=policyValue θ net plus minus (advantage v).1 (advantage v).2)
theorem _ThesisExactChecks.target_282 : _ThesisExpectedTypes.type_282 := by exact @Thesis.SoftplusGame.playerValue_advantage
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.playerValue_advantage
  let expected ← getConstInfo `_ThesisExactChecks.target_282
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.playerValue_advantage"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.playerValue_advantage | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusPlayerValues do
    throwError "Defining module mismatch: Thesis.SoftplusGame.playerValue_advantage"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_282) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.playerValue_advantage: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.playerValue_advantage"
#check @Thesis.SoftplusGame.playerValue_advantage
#print axioms _ThesisExactChecks.target_282

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_283 : Prop := (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : PairVec n), playerValue θ net (gibbsStrategy θ net (x.1-x.2)) (gibbsStrategy θ net (x.1-x.2)) (pairValues x)=pairValues (net.decomposeWith (fun z => softSplit θ z.1 z.2) x))
theorem _ThesisExactChecks.target_283 : _ThesisExpectedTypes.type_283 := by exact @Thesis.SoftplusGame.playerValue_gibbs
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.playerValue_gibbs
  let expected ← getConstInfo `_ThesisExactChecks.target_283
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.playerValue_gibbs"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.playerValue_gibbs | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusPlayerValues do
    throwError "Defining module mismatch: Thesis.SoftplusGame.playerValue_gibbs"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_283) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.playerValue_gibbs: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.playerValue_gibbs"
#check @Thesis.SoftplusGame.playerValue_gibbs
#print axioms _ThesisExactChecks.target_283

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_284 : Prop := (∀ {n m r : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net) (wp wn : Matrix (Fin r) (Fin m) ℝ) (hrow : ∀ j i,0≤wp j i ∧ 0≤wn j i) (b : Vec r) (j : Fin r),
 let read := fun v : PairVec m => continuation wp wn b v.1 v.2 j;
 read (policyValue θ net plus (gibbsStrategy θ net x) x (-x))≤affineOutput θ net (wp-wn) b x j ∧
 read (policyValue θ net (gibbsStrategy θ net x) (gibbsStrategy θ net x) x (-x))=affineOutput θ net (wp-wn) b x j ∧
 affineOutput θ net (wp-wn) b x j≤read (policyValue θ net (gibbsStrategy θ net x) minus x (-x)))
theorem _ThesisExactChecks.target_284 : _ThesisExpectedTypes.type_284 := by exact @Thesis.SoftplusGame.affine_saddle
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.affine_saddle
  let expected ← getConstInfo `_ThesisExactChecks.target_284
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.affine_saddle"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.affine_saddle | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusReadout do
    throwError "Defining module mismatch: Thesis.SoftplusGame.affine_saddle"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_284) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.affine_saddle: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.affine_saddle"
#check @Thesis.SoftplusGame.affine_saddle
#print axioms _ThesisExactChecks.target_284

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_285 : Prop := (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : PairVec n),
 SubgamePerfect θ net (gibbsStrategy θ net (x.1-x.2)) (gibbsStrategy θ net (x.1-x.2)) (x.1-x.2) (-(x.1-x.2)) ∧
 (∀ plus minus : Strategy net,SubgamePerfect θ net plus minus (x.1-x.2) (-(x.1-x.2)) ↔ plus=gibbsStrategy θ net (x.1-x.2) ∧ minus=gibbsStrategy θ net (x.1-x.2)) ∧
 playerValue θ net (gibbsStrategy θ net (x.1-x.2)) (gibbsStrategy θ net (x.1-x.2)) (pairValues x)=pairValues (net.decomposeWith (fun z => softSplit θ z.1 z.2) x) ∧
 (net.decomposeWith (fun z => softSplit θ z.1 z.2) x).1-(net.decomposeWith (fun z => softSplit θ z.1 z.2) x).2=softEval θ net (x.1-x.2))
theorem _ThesisExactChecks.target_285 : _ThesisExpectedTypes.type_285 := by exact @Thesis.SoftplusGame.softplus_forward_spne
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.softplus_forward_spne
  let expected ← getConstInfo `_ThesisExactChecks.target_285
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.softplus_forward_spne"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.softplus_forward_spne | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusReadout do
    throwError "Defining module mismatch: Thesis.SoftplusGame.softplus_forward_spne"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_285) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.softplus_forward_spne: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.softplus_forward_spne"
#check @Thesis.SoftplusGame.softplus_forward_spne
#print axioms _ThesisExactChecks.target_285

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_286 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (plus minus : Fin k → Set.Icc (0 : ℝ) 1) (j : Fin k) (i : Fin n) (r b : Bool), mixedTransition (if Bool.xor r b then minus j else plus j) wp wn j (Bool.xor r b) (some (i,r))=(if Bool.xor r b then (minus j).val else (plus j).val)*(if b then wn j i else wp j i)/fanIn wp wn j)
theorem _ThesisExactChecks.target_286 : _ThesisExpectedTypes.type_286 := by exact @Thesis.SoftplusGame.profile_step_transition
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.profile_step_transition
  let expected ← getConstInfo `_ThesisExactChecks.target_286
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.profile_step_transition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.profile_step_transition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusGameOccupation do
    throwError "Defining module mismatch: Thesis.SoftplusGame.profile_step_transition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_286) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.profile_step_transition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.profile_step_transition"
#check @Thesis.SoftplusGame.profile_step_transition
#print axioms _ThesisExactChecks.target_286

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_287 : Prop := (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (x : Vec n) (j : Fin m) (i : Fin n) (q r : Bool) (path : Paths (softTrace θ net x)), profileProbability θ net (gibbsStrategy θ net x) (gibbsStrategy θ net x) x j i q r path=softProbability θ net x j i (Bool.xor q r) path)
theorem _ThesisExactChecks.target_287 : _ThesisExpectedTypes.type_287 := by exact @Thesis.SoftplusGame.profileProbability_gibbs
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.profileProbability_gibbs
  let expected ← getConstInfo `_ThesisExactChecks.target_287
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.profileProbability_gibbs"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.profileProbability_gibbs | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusGameOccupation do
    throwError "Defining module mismatch: Thesis.SoftplusGame.profileProbability_gibbs"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_287) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.profileProbability_gibbs: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.profileProbability_gibbs"
#check @Thesis.SoftplusGame.profileProbability_gibbs
#print axioms _ThesisExactChecks.target_287

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_288 : Prop := (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net) (hsp : SubgamePerfect θ net plus minus x (-x)) (j : Fin m) (i : Fin n) (q r : Bool), profileOccupation net θ plus minus x j i q r=softOccupation net θ x j i (Bool.xor q r))
theorem _ThesisExactChecks.target_288 : _ThesisExpectedTypes.type_288 := by exact @Thesis.SoftplusGame.spne_occupation_eq
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.spne_occupation_eq
  let expected ← getConstInfo `_ThesisExactChecks.target_288
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.spne_occupation_eq"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.spne_occupation_eq | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusGameOccupation do
    throwError "Defining module mismatch: Thesis.SoftplusGame.spne_occupation_eq"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_288) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.spne_occupation_eq: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.spne_occupation_eq"
#check @Thesis.SoftplusGame.spne_occupation_eq
#print axioms _ThesisExactChecks.target_288

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_289 : Prop := (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net) (hsp : SubgamePerfect θ net plus minus x (-x)) (j : Fin m) (i : Fin n) (q : Bool), fderiv ℝ (softEval θ net) x (Pi.single i 1) j=(if q then (-1 : ℝ) else 1)*(profileOccupation net θ plus minus x j i q false-profileOccupation net θ plus minus x j i q true))
theorem _ThesisExactChecks.target_289 : _ThesisExpectedTypes.type_289 := by exact @Thesis.SoftplusGame.spne_gradient
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.spne_gradient
  let expected ← getConstInfo `_ThesisExactChecks.target_289
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.spne_gradient"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.spne_gradient | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusGameOccupation do
    throwError "Defining module mismatch: Thesis.SoftplusGame.spne_gradient"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_289) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.spne_gradient: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.spne_gradient"
#check @Thesis.SoftplusGame.spne_gradient
#print axioms _ThesisExactChecks.target_289

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_290 : Prop := (∀ {n m r : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net) (hsp : SubgamePerfect θ net plus minus x (-x)) (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (j : Fin r) (i : Fin n) (q : Bool), fderiv ℝ (affineOutput θ net C b) x (Pi.single i 1) j=∑ h,C j h*(if q then (-1 : ℝ) else 1)*(profileOccupation net θ plus minus x h i q false-profileOccupation net θ plus minus x h i q true))
theorem _ThesisExactChecks.target_290 : _ThesisExpectedTypes.type_290 := by exact @Thesis.SoftplusGame.spne_affine_gradient_profile
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.spne_affine_gradient_profile
  let expected ← getConstInfo `_ThesisExactChecks.target_290
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.spne_affine_gradient_profile"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.spne_affine_gradient_profile | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusGameOccupation do
    throwError "Defining module mismatch: Thesis.SoftplusGame.spne_affine_gradient_profile"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_290) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.spne_affine_gradient_profile: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.spne_affine_gradient_profile"
#check @Thesis.SoftplusGame.spne_affine_gradient_profile
#print axioms _ThesisExactChecks.target_290

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_291 : Prop := (∀ {a b c : ℕ} (pre : Network a b) (suffix : Network b c) (θ : ℝ) (x : Vec a), softEval θ (pre.append suffix) x=softEval θ suffix (softEval θ pre x))
theorem _ThesisExactChecks.target_291 : _ThesisExpectedTypes.type_291 := by exact @Thesis.SoftplusGame.softEval_append
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.softEval_append
  let expected ← getConstInfo `_ThesisExactChecks.target_291
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.softEval_append"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.softEval_append | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusSubgames do
    throwError "Defining module mismatch: Thesis.SoftplusGame.softEval_append"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_291) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.softEval_append: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.softEval_append"
#check @Thesis.SoftplusGame.softEval_append
#print axioms _ThesisExactChecks.target_291

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_292 : Prop := (∀ {a b c : ℕ} (pre : Network a b) (suffix : Network b c) (θ : ℝ) (hθ : 0<θ) (hp : pre.Nonnegative) (hs : suffix.Nonnegative) (x : Vec a) (plus minus : Strategy (pre.append suffix)) (hsp : SubgamePerfect θ (pre.append suffix) plus minus x (-x)), SubgamePerfect θ suffix (suffixStrategy pre suffix plus) (suffixStrategy pre suffix minus) (softEval θ pre x) (-(softEval θ pre x)))
theorem _ThesisExactChecks.target_292 : _ThesisExpectedTypes.type_292 := by exact @Thesis.SoftplusGame.spne_suffix
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.spne_suffix
  let expected ← getConstInfo `_ThesisExactChecks.target_292
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.spne_suffix"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.spne_suffix | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusSubgames do
    throwError "Defining module mismatch: Thesis.SoftplusGame.spne_suffix"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_292) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.spne_suffix: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.spne_suffix"
#check @Thesis.SoftplusGame.spne_suffix
#print axioms _ThesisExactChecks.target_292

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_293 : Prop := (∀ {a b c : ℕ} (pre : Network a b) (suffix : Network b c) (θ : ℝ) (hθ : 0<θ) (hp : pre.Nonnegative) (hs : suffix.Nonnegative) (x : Vec a) (plus minus : Strategy (pre.append suffix)) (hsp : SubgamePerfect θ (pre.append suffix) plus minus x (-x)) (plusDev minusDev : Strategy pre),
 (policyValue θ pre plusDev (prefixStrategy pre suffix minus) x (-x)).1 ≤ softEval θ pre x ∧
 (policyValue θ pre plusDev (prefixStrategy pre suffix minus) x (-x)).2 ≤ -softEval θ pre x ∧
 policyValue θ pre (prefixStrategy pre suffix plus) (prefixStrategy pre suffix minus) x (-x)=(softEval θ pre x,-softEval θ pre x) ∧
 softEval θ pre x ≤ (policyValue θ pre (prefixStrategy pre suffix plus) minusDev x (-x)).1 ∧
 -softEval θ pre x ≤ (policyValue θ pre (prefixStrategy pre suffix plus) minusDev x (-x)).2)
theorem _ThesisExactChecks.target_293 : _ThesisExpectedTypes.type_293 := by exact @Thesis.SoftplusGame.spne_prefix_saddle
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.spne_prefix_saddle
  let expected ← getConstInfo `_ThesisExactChecks.target_293
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.spne_prefix_saddle"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.spne_prefix_saddle | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusSubgames do
    throwError "Defining module mismatch: Thesis.SoftplusGame.spne_prefix_saddle"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_293) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.spne_prefix_saddle: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.spne_prefix_saddle"
#check @Thesis.SoftplusGame.spne_prefix_saddle
#print axioms _ThesisExactChecks.target_293

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_294 : Prop := (∀ {a b c : ℕ} (pre : Network a b) (suffix : Network b c) (θ : ℝ) (hθ : 0<θ) (hp : pre.Nonnegative) (hs : suffix.Nonnegative) (x : Vec a) (plus minus : Strategy (pre.append suffix)) (hsp : SubgamePerfect θ (pre.append suffix) plus minus x (-x)) (j : Fin c) (i : Fin b) (q : Bool),
 fderiv ℝ (softEval θ suffix) (softEval θ pre x) (Pi.single i 1) j=(if q then (-1 : ℝ) else 1)*(profileOccupation suffix θ (suffixStrategy pre suffix plus) (suffixStrategy pre suffix minus) (softEval θ pre x) j i q false-profileOccupation suffix θ (suffixStrategy pre suffix plus) (suffixStrategy pre suffix minus) (softEval θ pre x) j i q true))
theorem _ThesisExactChecks.target_294 : _ThesisExpectedTypes.type_294 := by exact @Thesis.SoftplusGame.spne_intermediate_gradient
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.spne_intermediate_gradient
  let expected ← getConstInfo `_ThesisExactChecks.target_294
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.spne_intermediate_gradient"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.spne_intermediate_gradient | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusSubgames do
    throwError "Defining module mismatch: Thesis.SoftplusGame.spne_intermediate_gradient"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_294) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.spne_intermediate_gradient: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.spne_intermediate_gradient"
#check @Thesis.SoftplusGame.spne_intermediate_gradient
#print axioms _ThesisExactChecks.target_294

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_295 : Prop := (∀ {n k : ℕ} (r : Set.Icc (0 : ℝ) 1) (wp wn : Matrix (Fin k) (Fin n) ℝ) (j : Fin k) (turn : Bool) (v : Bool → Vec n), (∑ target : Option (Fin n × Bool),mixedTransition r wp wn j turn target*target.elim 0 (fun t => v t.2 t.1))=r.val*∑ i,(wp j i/rowDiscount wp wn j*v turn i+wn j i/rowDiscount wp wn j*v (!turn) i))
theorem _ThesisExactChecks.target_295 : _ThesisExpectedTypes.type_295 := by exact @Thesis.SoftplusGame.mixed_expected_value
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.mixed_expected_value
  let expected ← getConstInfo `_ThesisExactChecks.target_295
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.mixed_expected_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.mixed_expected_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusTransitionPayoff do
    throwError "Defining module mismatch: Thesis.SoftplusGame.mixed_expected_value"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_295) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.mixed_expected_value: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.mixed_expected_value"
#check @Thesis.SoftplusGame.mixed_expected_value
#print axioms _ThesisExactChecks.target_295

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
def _ThesisExpectedTypes.type_296 : Prop := (∀ {n k : ℕ} (θ : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (plus minus : Fin k → Set.Icc (0 : ℝ) 1) (v : PlayerValues n) (player turn : Bool) (j : Fin k), let r := if turn then minus j else plus j; playerStep θ wp wn bp bn plus minus v player turn j=r.val*(if player=turn then bp j else bn j)+(if player=turn then θ*Real.binEntropy r.val else 0)+rowDiscount wp wn j*∑ target : Option (Fin n × Bool),mixedTransition r wp wn j turn target*target.elim 0 (fun t => v player t.2 t.1))
theorem _ThesisExactChecks.target_296 : _ThesisExpectedTypes.type_296 := by exact @Thesis.SoftplusGame.playerStep_transition
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusGame.playerStep_transition
  let expected ← getConstInfo `_ThesisExactChecks.target_296
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusGame.playerStep_transition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusGame.playerStep_transition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusTransitionPayoff do
    throwError "Defining module mismatch: Thesis.SoftplusGame.playerStep_transition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_296) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusGame.playerStep_transition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusGame.playerStep_transition"
#check @Thesis.SoftplusGame.playerStep_transition
#print axioms _ThesisExactChecks.target_296

section
open Thesis.Games Thesis.ConditionedSurvival
open scoped BigOperators
def _ThesisExpectedTypes.type_297 : Prop := (∀ {S : Type} [Fintype S] (n : ℕ) (K : ℕ → S → S → ℝ)
(h : ℕ → S → ℝ) (hK : ∀ i s t, 0 ≤ K i s t)
(hh : ∀ i s, 0 ≤ h i s)
(hrec : ∀ i < n, ∀ s, h i s = ∑ t, K i s t * h (i+1) t)
(s : S) (path : Paths S n),
pathLaw n (kernel K h) s path * h 0 s =
pathLaw n K s path * h n (endpoint n s path))
theorem _ThesisExactChecks.target_297 : _ThesisExpectedTypes.type_297 := by exact @Thesis.ConditionedSurvival.weighted_path_identity
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.weighted_path_identity
  let expected ← getConstInfo `_ThesisExactChecks.target_297
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.weighted_path_identity"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.weighted_path_identity | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedSurvival do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.weighted_path_identity"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_297) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.weighted_path_identity: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.weighted_path_identity"
#check @Thesis.ConditionedSurvival.weighted_path_identity
#print axioms _ThesisExactChecks.target_297

section
open Thesis.Games Thesis.ConditionedSurvival
open scoped BigOperators
def _ThesisExpectedTypes.type_298 : Prop := (∀ {S : Type} (n : ℕ) (K : ℕ → S → S → ℝ)
(h : ℕ → S → ℝ) (hh : ∀ i s, 0 ≤ h i s)
(s : S) (hs : 0 < h 0 s) (path : Paths S n) (i : ℕ) (hi : i ≤ n)
(hz : h i (stateAt n s path i) = 0),
pathLaw n (kernel K h) s path = 0)
theorem _ThesisExactChecks.target_298 : _ThesisExpectedTypes.type_298 := by exact @Thesis.ConditionedSurvival.path_zero_at_zero_potential
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.path_zero_at_zero_potential
  let expected ← getConstInfo `_ThesisExactChecks.target_298
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.path_zero_at_zero_potential"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.path_zero_at_zero_potential | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedSurvival do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.path_zero_at_zero_potential"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_298) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.path_zero_at_zero_potential: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.path_zero_at_zero_potential"
#check @Thesis.ConditionedSurvival.path_zero_at_zero_potential
#print axioms _ThesisExactChecks.target_298

section
open Thesis.Games Thesis.ConditionedSurvival
open scoped BigOperators
def _ThesisExpectedTypes.type_299 : Prop := (∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ)
(i : ℕ) (hi : i < N) (s : S),
survival N K i s = ∑ t, K i s t * survival N K (i+1) t)
theorem _ThesisExactChecks.target_299 : _ThesisExpectedTypes.type_299 := by exact @Thesis.ConditionedSurvival.survival_recurrence
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.survival_recurrence
  let expected ← getConstInfo `_ThesisExactChecks.target_299
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.survival_recurrence"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.survival_recurrence | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedSurvival do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.survival_recurrence"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_299) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.survival_recurrence: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.survival_recurrence"
#check @Thesis.ConditionedSurvival.survival_recurrence
#print axioms _ThesisExactChecks.target_299

section
open Thesis.Games Thesis.ConditionedSurvival
open scoped BigOperators
def _ThesisExpectedTypes.type_300 : Prop := (∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ) (s : S),
survival N K 0 s = ∑ path : Paths S N, pathLaw N K s path)
theorem _ThesisExactChecks.target_300 : _ThesisExpectedTypes.type_300 := by exact @Thesis.ConditionedSurvival.survival_eq_path_mass
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.survival_eq_path_mass
  let expected ← getConstInfo `_ThesisExactChecks.target_300
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.survival_eq_path_mass"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.survival_eq_path_mass | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedSurvival do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.survival_eq_path_mass"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_300) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.survival_eq_path_mass: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.survival_eq_path_mass"
#check @Thesis.ConditionedSurvival.survival_eq_path_mass
#print axioms _ThesisExactChecks.target_300

section
open Thesis.Games Thesis.ConditionedSurvival
open scoped BigOperators
def _ThesisExpectedTypes.type_301 : Prop := (∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ)
(hK : ∀ i s t, 0 ≤ K i s t) (s : S) (hs : survival N K 0 s = 0)
(path : Paths S N), pathLaw N K s path = 0)
theorem _ThesisExactChecks.target_301 : _ThesisExpectedTypes.type_301 := by exact @Thesis.ConditionedSurvival.survival_zero_path
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.survival_zero_path
  let expected ← getConstInfo `_ThesisExactChecks.target_301
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.survival_zero_path"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.survival_zero_path | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedSurvival do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.survival_zero_path"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_301) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.survival_zero_path: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.survival_zero_path"
#check @Thesis.ConditionedSurvival.survival_zero_path
#print axioms _ThesisExactChecks.target_301

section
open Thesis.Games Thesis.ConditionedSurvival
open scoped BigOperators
def _ThesisExpectedTypes.type_302 : Prop := (∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ)
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
pathLaw N (kernel K (survival N K)) s path = 0))
theorem _ThesisExactChecks.target_302 : _ThesisExpectedTypes.type_302 := by exact @Thesis.ConditionedSurvival.conditioned_survival
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.conditioned_survival
  let expected ← getConstInfo `_ThesisExactChecks.target_302
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.conditioned_survival"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.conditioned_survival | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedSurvival do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.conditioned_survival"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_302) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.conditioned_survival: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.conditioned_survival"
#check @Thesis.ConditionedSurvival.conditioned_survival
#print axioms _ThesisExactChecks.target_302

section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
open scoped BigOperators
def _ThesisExpectedTypes.type_303 : Prop := (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (p : Policy A) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i),
objective reference contribution p = sourceValue 1 (mass reference contribution) p)
theorem _ThesisExactChecks.target_303 : _ThesisExpectedTypes.type_303.{u} := by exact @Thesis.AttentionReference.objective_eq_sourceValue.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.AttentionReference.objective_eq_sourceValue
  let expected ← getConstInfo `_ThesisExactChecks.target_303
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.AttentionReference.objective_eq_sourceValue"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AttentionReference.objective_eq_sourceValue | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AttentionReference do
    throwError "Defining module mismatch: Thesis.AttentionReference.objective_eq_sourceValue"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_303) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AttentionReference.objective_eq_sourceValue: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AttentionReference.objective_eq_sourceValue"
#check @Thesis.AttentionReference.objective_eq_sourceValue
#print axioms _ThesisExactChecks.target_303

section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
open scoped BigOperators
def _ThesisExpectedTypes.type_304 : Prop := (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i) (hz : 0 < ∑ i, mass reference contribution i),
objective reference contribution (valuePolicy reference contribution hr hc hz) = (Real.log (∑ i, reference i * contribution i) : WithBot ℝ))
theorem _ThesisExactChecks.target_304 : _ThesisExpectedTypes.type_304.{u} := by exact @Thesis.AttentionReference.valuePolicy_value.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.AttentionReference.valuePolicy_value
  let expected ← getConstInfo `_ThesisExactChecks.target_304
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.AttentionReference.valuePolicy_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AttentionReference.valuePolicy_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AttentionReference do
    throwError "Defining module mismatch: Thesis.AttentionReference.valuePolicy_value"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_304) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AttentionReference.valuePolicy_value: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AttentionReference.valuePolicy_value"
#check @Thesis.AttentionReference.valuePolicy_value
#print axioms _ThesisExactChecks.target_304

section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
open scoped BigOperators
def _ThesisExpectedTypes.type_305 : Prop := (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (p : Policy A) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i) (hz : 0 < ∑ i, mass reference contribution i),
objective reference contribution p = (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ↔ p.prob = (valuePolicy reference contribution hr hc hz).prob)
theorem _ThesisExactChecks.target_305 : _ThesisExpectedTypes.type_305.{u} := by exact @Thesis.AttentionReference.valuePolicy_unique.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.AttentionReference.valuePolicy_unique
  let expected ← getConstInfo `_ThesisExactChecks.target_305
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.AttentionReference.valuePolicy_unique"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AttentionReference.valuePolicy_unique | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AttentionReference do
    throwError "Defining module mismatch: Thesis.AttentionReference.valuePolicy_unique"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_305) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AttentionReference.valuePolicy_unique: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AttentionReference.valuePolicy_unique"
#check @Thesis.AttentionReference.valuePolicy_unique
#print axioms _ThesisExactChecks.target_305

section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
open scoped BigOperators
def _ThesisExpectedTypes.type_306 : Prop := (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (p : Policy A) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i)
(hz : (∑ i, reference i * contribution i) = 0),
objective reference contribution p = ⊥)
theorem _ThesisExactChecks.target_306 : _ThesisExpectedTypes.type_306.{u} := by exact @Thesis.AttentionReference.zero_mass_value.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.AttentionReference.zero_mass_value
  let expected ← getConstInfo `_ThesisExactChecks.target_306
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.AttentionReference.zero_mass_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AttentionReference.zero_mass_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AttentionReference do
    throwError "Defining module mismatch: Thesis.AttentionReference.zero_mass_value"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_306) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AttentionReference.zero_mass_value: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AttentionReference.zero_mass_value"
#check @Thesis.AttentionReference.zero_mass_value
#print axioms _ThesisExactChecks.target_306

section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
open scoped BigOperators
def _ThesisExpectedTypes.type_307 : Prop := (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i) (hz : 0 < ∑ i, mass reference contribution i),
IsGreatest (Set.range (objective reference contribution)) (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ∧
(∀ p : Policy A, objective reference contribution p = (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ↔ p.prob = (valuePolicy reference contribution hr hc hz).prob) ∧
(∀ i, (valuePolicy reference contribution hr hc hz).prob i = reference i * contribution i / ∑ j, reference j * contribution j))
theorem _ThesisExactChecks.target_307 : _ThesisExpectedTypes.type_307.{u} := by exact @Thesis.AttentionReference.attention_value_routing.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.AttentionReference.attention_value_routing
  let expected ← getConstInfo `_ThesisExactChecks.target_307
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.AttentionReference.attention_value_routing"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AttentionReference.attention_value_routing | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AttentionReference do
    throwError "Defining module mismatch: Thesis.AttentionReference.attention_value_routing"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_307) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AttentionReference.attention_value_routing: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AttentionReference.attention_value_routing"
#check @Thesis.AttentionReference.attention_value_routing
#print axioms _ThesisExactChecks.target_307

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_308 := (∀ {n : ℕ}, ℝ → Sensitivity n → Sensitivity n)
noncomputable def _ThesisExactChecks.target_308 : _ThesisExpectedTypes.type_308 := by exact @HiddenMonotonicity.shiftPair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.shiftPair
  let expected ← getConstInfo `_ThesisExactChecks.target_308
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.shiftPair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.shiftPair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.StabilizedBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.shiftPair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_308) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.shiftPair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.shiftPair"
#check @HiddenMonotonicity.shiftPair
#print axioms _ThesisExactChecks.target_308

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_309 := (∀ {n : ℕ}, Sensitivity n → Row n)
noncomputable def _ThesisExactChecks.target_309 : _ThesisExpectedTypes.type_309 := by exact @HiddenMonotonicity.unified
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.unified
  let expected ← getConstInfo `_ThesisExactChecks.target_309
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.unified"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.unified | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.StabilizedBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.unified"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_309) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.unified: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.unified"
#check @HiddenMonotonicity.unified
#print axioms _ThesisExactChecks.target_309

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_310 : Prop := (∀ {n : ℕ} (α : ℝ) (s : Sensitivity n), (shiftPair α s).1+(shiftPair α s).2 = (1-2*α) • (s.1+s.2))
theorem _ThesisExactChecks.target_310 : _ThesisExpectedTypes.type_310 := by exact @HiddenMonotonicity.shiftPair_sum
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.shiftPair_sum
  let expected ← getConstInfo `_ThesisExactChecks.target_310
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.shiftPair_sum"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.shiftPair_sum | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.StabilizedBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.shiftPair_sum"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_310) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.shiftPair_sum: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.shiftPair_sum"
#check @HiddenMonotonicity.shiftPair_sum
#print axioms _ThesisExactChecks.target_310

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_311 : Prop := (∀ {n : ℕ} (α : ℝ) (s : Sensitivity n), unified (shiftPair α s)=unified s)
theorem _ThesisExactChecks.target_311 : _ThesisExpectedTypes.type_311 := by exact @HiddenMonotonicity.unified_shift
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.unified_shift
  let expected ← getConstInfo `_ThesisExactChecks.target_311
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.unified_shift"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.unified_shift | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.StabilizedBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.unified_shift"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_311) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.unified_shift: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.unified_shift"
#check @HiddenMonotonicity.unified_shift
#print axioms _ThesisExactChecks.target_311

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_312 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (gate : Fin k → Bool) (s : Sensitivity k), unified (MaskedTrace.pull wp wn gate s)=(unified s).comp (MaskedTrace.signedMap wp wn gate)-(1/2 : ℝ) • ((s.1+s.2).comp (MaskedTrace.deadMap wp wn gate)))
theorem _ThesisExactChecks.target_312 : _ThesisExpectedTypes.type_312 := by exact @HiddenMonotonicity.MaskedTrace.pull_unified
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaskedTrace.pull_unified
  let expected ← getConstInfo `_ThesisExactChecks.target_312
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaskedTrace.pull_unified"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaskedTrace.pull_unified | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.StabilizedBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.MaskedTrace.pull_unified"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_312) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaskedTrace.pull_unified: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaskedTrace.pull_unified"
#check @HiddenMonotonicity.MaskedTrace.pull_unified
#print axioms _ThesisExactChecks.target_312

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_313 : Prop := (∀ {n m : ℕ} (tr : MaskedTrace n m) (α : ℕ → ℝ) (seed : Sensitivity m), (tr.run α seed).1+(tr.run α seed).2=tr.bulkCoefficient α • ((seed.1+seed.2).comp tr.absMap))
theorem _ThesisExactChecks.target_313 : _ThesisExpectedTypes.type_313 := by exact @HiddenMonotonicity.MaskedTrace.run_bulk
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaskedTrace.run_bulk
  let expected ← getConstInfo `_ThesisExactChecks.target_313
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaskedTrace.run_bulk"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaskedTrace.run_bulk | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.AffineReadout do
    throwError "Defining module mismatch: HiddenMonotonicity.MaskedTrace.run_bulk"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_313) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaskedTrace.run_bulk: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaskedTrace.run_bulk"
#check @HiddenMonotonicity.MaskedTrace.run_bulk
#print axioms _ThesisExactChecks.target_313

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_314 : Prop := (∀ {n m : ℕ} (tr : MaskedTrace n m) (α : ℕ → ℝ), tr.bulkCoefficient α=∏ i ∈ Finset.range (tr.depth+1), (1-2*α i))
theorem _ThesisExactChecks.target_314 : _ThesisExpectedTypes.type_314 := by exact @HiddenMonotonicity.MaskedTrace.bulkCoefficient_product
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaskedTrace.bulkCoefficient_product
  let expected ← getConstInfo `_ThesisExactChecks.target_314
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaskedTrace.bulkCoefficient_product"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaskedTrace.bulkCoefficient_product | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.StabilizedBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.MaskedTrace.bulkCoefficient_product"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_314) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaskedTrace.bulkCoefficient_product: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaskedTrace.bulkCoefficient_product"
#check @HiddenMonotonicity.MaskedTrace.bulkCoefficient_product
#print axioms _ThesisExactChecks.target_314

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_315 := (∀ {n k : ℕ}, Matrix (Fin k) (Fin n) ℝ → Matrix (Fin k) (Fin n) ℝ → Vec k → Vec k → PairVec n → PairVec k)
noncomputable def _ThesisExactChecks.target_315 : _ThesisExpectedTypes.type_315 := by exact @HiddenMonotonicity.affineChunk
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.affineChunk
  let expected ← getConstInfo `_ThesisExactChecks.target_315
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.affineChunk"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.affineChunk | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.AffineChunk do
    throwError "Defining module mismatch: HiddenMonotonicity.affineChunk"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_315) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.affineChunk: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.affineChunk"
#check @HiddenMonotonicity.affineChunk
#print axioms _ThesisExactChecks.target_315

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_316 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (x : PairVec n), preP wp wn x+bp-(preN wp wn x+bn)=affineLayer wp wn bp bn (x.1-x.2))
theorem _ThesisExactChecks.target_316 : _ThesisExpectedTypes.type_316 := by exact @HiddenMonotonicity.preactivation_difference
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.preactivation_difference
  let expected ← getConstInfo `_ThesisExactChecks.target_316
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.preactivation_difference"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.preactivation_difference | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.OriginalTrace do
    throwError "Defining module mismatch: HiddenMonotonicity.preactivation_difference"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_316) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.preactivation_difference: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.preactivation_difference"
#check @HiddenMonotonicity.preactivation_difference
#print axioms _ThesisExactChecks.target_316

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_317 := (ℝ → (ℝ × ℝ) → ℝ × ℝ)
noncomputable def _ThesisExactChecks.target_317 : _ThesisExpectedTypes.type_317 := by exact @HiddenMonotonicity.mixPair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.mixPair
  let expected ← getConstInfo `_ThesisExactChecks.target_317
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.mixPair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.mixPair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Decomposition do
    throwError "Defining module mismatch: HiddenMonotonicity.mixPair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_317) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.mixPair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.mixPair"
#check @HiddenMonotonicity.mixPair
#print axioms _ThesisExactChecks.target_317

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_318 : Prop := (∀ p n : ℝ, max p n-n=relu (p-n))
theorem _ThesisExactChecks.target_318 : _ThesisExpectedTypes.type_318 := by exact @HiddenMonotonicity.max_sub
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.max_sub
  let expected ← getConstInfo `_ThesisExactChecks.target_318
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.max_sub"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.max_sub | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Core do
    throwError "Defining module mismatch: HiddenMonotonicity.max_sub"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_318) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.max_sub: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.max_sub"
#check @HiddenMonotonicity.max_sub
#print axioms _ThesisExactChecks.target_318

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_319 := (∀ {n k : ℕ}, Matrix (Fin k) (Fin n) ℝ → Matrix (Fin k) (Fin n) ℝ → Vec k → Vec k → PairVec n → PairVec k)
noncomputable def _ThesisExactChecks.target_319 : _ThesisExpectedTypes.type_319 := by exact @HiddenMonotonicity.layerFun
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.layerFun
  let expected ← getConstInfo `_ThesisExactChecks.target_319
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.layerFun"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.layerFun | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.NetworkDerivative do
    throwError "Defining module mismatch: HiddenMonotonicity.layerFun"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_319) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.layerFun: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.layerFun"
#check @HiddenMonotonicity.layerFun
#print axioms _ThesisExactChecks.target_319

section
universe u
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_320 := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] [DecidableEq ι], ((ι → ℝ) × (ι → ℝ)) → ℝ × ℝ)
noncomputable def _ThesisExactChecks.target_320 : _ThesisExpectedTypes.type_320.{u} := by exact @HiddenMonotonicity.finitePool.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.finitePool
  let expected ← getConstInfo `_ThesisExactChecks.target_320
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.finitePool"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.finitePool | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MaxPool do
    throwError "Defining module mismatch: HiddenMonotonicity.finitePool"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_320) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.finitePool: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.finitePool"
#check @HiddenMonotonicity.finitePool
#print axioms _ThesisExactChecks.target_320

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_321 : Prop := (∀ p q r s : ℝ, (p*r+q*s)-(p*s+q*r)=(p-q)*(r-s))
theorem _ThesisExactChecks.target_321 : _ThesisExpectedTypes.type_321 := by exact @HiddenMonotonicity.multiplicative_split_correct
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.multiplicative_split_correct
  let expected ← getConstInfo `_ThesisExactChecks.target_321
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.multiplicative_split_correct"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.multiplicative_split_correct | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Chunks do
    throwError "Defining module mismatch: HiddenMonotonicity.multiplicative_split_correct"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_321) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.multiplicative_split_correct: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.multiplicative_split_correct"
#check @HiddenMonotonicity.multiplicative_split_correct
#print axioms _ThesisExactChecks.target_321

section
open HiddenMonotonicity Thesis.StoppingDecomposition
open scoped BigOperators
def _ThesisExpectedTypes.type_322 := ((ℝ × ℝ) → ℝ × ℝ)
noncomputable def _ThesisExactChecks.target_322 : _ThesisExpectedTypes.type_322 := by exact @Thesis.StoppingDecomposition.stopPair
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDecomposition.stopPair
  let expected ← getConstInfo `_ThesisExactChecks.target_322
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDecomposition.stopPair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDecomposition.stopPair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDecomposition do
    throwError "Defining module mismatch: Thesis.StoppingDecomposition.stopPair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_322) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDecomposition.stopPair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDecomposition.stopPair"
#check @Thesis.StoppingDecomposition.stopPair
#print axioms _ThesisExactChecks.target_322

section
open HiddenMonotonicity Thesis.StoppingDecomposition
open scoped BigOperators
def _ThesisExpectedTypes.type_323 := (∀ {n k : ℕ}, Matrix (Fin k) (Fin n) ℝ → Matrix (Fin k) (Fin n) ℝ → Vec k → Vec k → PairVec n → PairVec k)
noncomputable def _ThesisExactChecks.target_323 : _ThesisExpectedTypes.type_323 := by exact @Thesis.StoppingDecomposition.stopLayer
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDecomposition.stopLayer
  let expected ← getConstInfo `_ThesisExactChecks.target_323
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDecomposition.stopLayer"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDecomposition.stopLayer | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDecomposition do
    throwError "Defining module mismatch: Thesis.StoppingDecomposition.stopLayer"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_323) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDecomposition.stopLayer: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDecomposition.stopLayer"
#check @Thesis.StoppingDecomposition.stopLayer
#print axioms _ThesisExactChecks.target_323

section
open HiddenMonotonicity Thesis.GeneralRegularization
open scoped BigOperators
def _ThesisExpectedTypes.type_324 := (Regularizer → (ℝ → ℝ) → (ℝ × ℝ) → ℝ × ℝ)
noncomputable def _ThesisExactChecks.target_324 : _ThesisExpectedTypes.type_324 := by exact @Thesis.GeneralRegularization.pairWith
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.pairWith
  let expected ← getConstInfo `_ThesisExactChecks.target_324
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.pairWith"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.pairWith | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.pairWith"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_324) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.pairWith: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.pairWith"
#check @Thesis.GeneralRegularization.pairWith
#print axioms _ThesisExactChecks.target_324

section
open HiddenMonotonicity Thesis.GeneralRegularization
open scoped BigOperators
def _ThesisExpectedTypes.type_325 := (∀ θ : ℝ, 0<θ → Regularizer)
noncomputable def _ThesisExactChecks.target_325 : _ThesisExpectedTypes.type_325 := by exact @Thesis.GeneralRegularization.entropyRegularizer
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.entropyRegularizer
  let expected ← getConstInfo `_ThesisExactChecks.target_325
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.entropyRegularizer"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.entropyRegularizer | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.entropyRegularizer"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_325) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.entropyRegularizer: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.entropyRegularizer"
#check @Thesis.GeneralRegularization.entropyRegularizer
#print axioms _ThesisExactChecks.target_325

section
open HiddenMonotonicity Thesis.GeneralRegularization
open scoped BigOperators
def _ThesisExpectedTypes.type_326 : Prop := (∀ z : ℝ, hardGate z ∈ Set.Icc (0 : ℝ) 1 ∧ IsMaxOn (objective zeroRegularizer z) (Set.Icc 0 1) (hardGate z))
theorem _ThesisExactChecks.target_326 : _ThesisExpectedTypes.type_326 := by exact @Thesis.GeneralRegularization.hardGate_optimal
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.hardGate_optimal
  let expected ← getConstInfo `_ThesisExactChecks.target_326
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.hardGate_optimal"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.hardGate_optimal | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.hardGate_optimal"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_326) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.hardGate_optimal: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.hardGate_optimal"
#check @Thesis.GeneralRegularization.hardGate_optimal
#print axioms _ThesisExactChecks.target_326

section
open HiddenMonotonicity Thesis.Regularization
open scoped BigOperators
def _ThesisExpectedTypes.type_327 := (ℝ → ℝ → ℝ → ℝ × ℝ)
noncomputable def _ThesisExactChecks.target_327 : _ThesisExpectedTypes.type_327 := by exact @Thesis.Regularization.softSplit
end
run_cmd do
  let target ← getConstInfo `Thesis.Regularization.softSplit
  let expected ← getConstInfo `_ThesisExactChecks.target_327
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Regularization.softSplit"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Regularization.softSplit | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Regularization do
    throwError "Defining module mismatch: Thesis.Regularization.softSplit"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_327) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Regularization.softSplit: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Regularization.softSplit"
#check @Thesis.Regularization.softSplit
#print axioms _ThesisExactChecks.target_327

section
open HiddenMonotonicity Thesis.Regularization
open scoped BigOperators
def _ThesisExpectedTypes.type_328 : Prop := (∀ (θ z : ℝ) (hθ : 0<θ), gate θ z*z+θ*Real.binEntropy (gate θ z)=softplus θ z)
theorem _ThesisExactChecks.target_328 : _ThesisExpectedTypes.type_328 := by exact @Thesis.Regularization.entropy_gate_value
end
run_cmd do
  let target ← getConstInfo `Thesis.Regularization.entropy_gate_value
  let expected ← getConstInfo `_ThesisExactChecks.target_328
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Regularization.entropy_gate_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Regularization.entropy_gate_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Regularization do
    throwError "Defining module mismatch: Thesis.Regularization.entropy_gate_value"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_328) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Regularization.entropy_gate_value: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Regularization.entropy_gate_value"
#check @Thesis.Regularization.entropy_gate_value
#print axioms _ThesisExactChecks.target_328

section
universe u
open HiddenMonotonicity Thesis.ReferencePolicy
open scoped BigOperators
def _ThesisExpectedTypes.type_329 : Prop := (∀ {A : Type u} [Fintype A] (ρ u : A → ℝ) (hu : ∀ i,0<u i), referencePolicy 1 ρ (fun i => Real.log (u i))=(fun i => ρ i*u i/∑ j,ρ j*u j))
theorem _ThesisExactChecks.target_329 : _ThesisExpectedTypes.type_329.{u} := by exact @Thesis.ReferencePolicy.reference_log_policy.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.ReferencePolicy.reference_log_policy
  let expected ← getConstInfo `_ThesisExactChecks.target_329
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.ReferencePolicy.reference_log_policy"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReferencePolicy.reference_log_policy | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReferencePolicy do
    throwError "Defining module mismatch: Thesis.ReferencePolicy.reference_log_policy"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_329) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ReferencePolicy.reference_log_policy: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReferencePolicy.reference_log_policy"
#check @Thesis.ReferencePolicy.reference_log_policy
#print axioms _ThesisExactChecks.target_329

section
universe u
open HiddenMonotonicity Thesis.ReferencePolicy
open scoped BigOperators
def _ThesisExpectedTypes.type_330 : Prop := (∀ {A : Type u} [Fintype A] [Nonempty A] (θ : ℝ) (ρ q : A → ℝ) (hθ : 0<θ) (hρ : ∀ i,0<ρ i), (∑ i,referencePolicy θ ρ q i*q i)-θ*kl (referencePolicy θ ρ q) ρ=referenceValue θ ρ q)
theorem _ThesisExactChecks.target_330 : _ThesisExpectedTypes.type_330.{u} := by exact @Thesis.ReferencePolicy.reference_policy_value.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.ReferencePolicy.reference_policy_value
  let expected ← getConstInfo `_ThesisExactChecks.target_330
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.ReferencePolicy.reference_policy_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReferencePolicy.reference_policy_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReferencePolicy do
    throwError "Defining module mismatch: Thesis.ReferencePolicy.reference_policy_value"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_330) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ReferencePolicy.reference_policy_value: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReferencePolicy.reference_policy_value"
#check @Thesis.ReferencePolicy.reference_policy_value
#print axioms _ThesisExactChecks.target_330

section
universe u v
open HiddenMonotonicity Thesis.Games
open scoped BigOperators
def _ThesisExpectedTypes.type_331 : Prop := (∀ {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] [DecidableEq Y] (p q : X → ℝ) (terminal : X → Y) (y : Y), pixelDisagreement p q terminal y=((∑ x,if terminal x=y then p x else 0)+(∑ x,if terminal x=y then q x else 0))/2-∑ x,if terminal x=y then Real.sqrt (p x*q x) else 0)
theorem _ThesisExactChecks.target_331 : _ThesisExpectedTypes.type_331.{u, v} := by exact @Thesis.Games.pixelDisagreement_formula.{u, v}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.pixelDisagreement_formula
  let expected ← getConstInfo `_ThesisExactChecks.target_331
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: Thesis.Games.pixelDisagreement_formula"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.pixelDisagreement_formula | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.pixelDisagreement_formula"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_331) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.pixelDisagreement_formula: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.pixelDisagreement_formula"
#check @Thesis.Games.pixelDisagreement_formula
#print axioms _ThesisExactChecks.target_331

section
universe u v
open HiddenMonotonicity Thesis.Games
open scoped BigOperators
def _ThesisExpectedTypes.type_332 : Prop := (∀ {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] [DecidableEq Y] (p q : X → ℝ) (terminal : X → Y) (hp1 : ∑ x,p x=1) (hq1 : ∑ x,q x=1), (∑ y,pixelDisagreement p q terminal y)=1-overlap p q)
theorem _ThesisExactChecks.target_332 : _ThesisExpectedTypes.type_332.{u, v} := by exact @Thesis.Games.pixelDisagreement_total.{u, v}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.pixelDisagreement_total
  let expected ← getConstInfo `_ThesisExactChecks.target_332
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: Thesis.Games.pixelDisagreement_total"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.pixelDisagreement_total | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.pixelDisagreement_total"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_332) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.pixelDisagreement_total: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.pixelDisagreement_total"
#check @Thesis.Games.pixelDisagreement_total
#print axioms _ThesisExactChecks.target_332

section
universe u
open HiddenMonotonicity Thesis.Games
open scoped BigOperators
def _ThesisExpectedTypes.type_333 : Prop := (∀ {S : Type u} [Fintype S] (p q : S → ℝ) (hp : ∀ s,0≤p s) (hq : ∀ s,0≤q s) (hp1 : ∑ s,p s=1) (hq1 : ∑ s,q s=1), overlap p q≤1)
theorem _ThesisExactChecks.target_333 : _ThesisExpectedTypes.type_333.{u} := by exact @Thesis.Games.overlap_le_one.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.overlap_le_one
  let expected ← getConstInfo `_ThesisExactChecks.target_333
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Games.overlap_le_one"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.overlap_le_one | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.overlap_le_one"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_333) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.overlap_le_one: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.overlap_le_one"
#check @Thesis.Games.overlap_le_one
#print axioms _ThesisExactChecks.target_333

section
universe u
open HiddenMonotonicity Thesis.Games
open scoped BigOperators
def _ThesisExpectedTypes.type_334 : Prop := (∀ {S : Type u} [Fintype S] (p q : S → ℝ), 0≤overlap p q)
theorem _ThesisExactChecks.target_334 : _ThesisExpectedTypes.type_334.{u} := by exact @Thesis.Games.overlap_nonneg.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.overlap_nonneg
  let expected ← getConstInfo `_ThesisExactChecks.target_334
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Games.overlap_nonneg"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.overlap_nonneg | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.overlap_nonneg"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_334) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.overlap_nonneg: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.overlap_nonneg"
#check @Thesis.Games.overlap_nonneg
#print axioms _ThesisExactChecks.target_334

section
open HiddenMonotonicity Thesis.RoutingSupport
open scoped BigOperators
def _ThesisExpectedTypes.type_335 := (∀ {n k : ℕ}, Matrix (Fin k) (Fin n) ℝ → Matrix (Fin k) (Fin n) ℝ → Vec k → Vec k → ℝ → ℝ → ℝ → Vec n → Matrix (Fin k) (Fin n) ℝ)
noncomputable def _ThesisExactChecks.target_335 : _ThesisExpectedTypes.type_335 := by exact @Thesis.RoutingSupport.sourceLayer
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingSupport.sourceLayer
  let expected ← getConstInfo `_ThesisExactChecks.target_335
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingSupport.sourceLayer"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingSupport.sourceLayer | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingSupport do
    throwError "Defining module mismatch: Thesis.RoutingSupport.sourceLayer"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_335) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingSupport.sourceLayer: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingSupport.sourceLayer"
#check @Thesis.RoutingSupport.sourceLayer
#print axioms _ThesisExactChecks.target_335

section
open HiddenMonotonicity Thesis.RoutingSupport
open scoped BigOperators
def _ThesisExpectedTypes.type_336 := (∀ {n m : ℕ}, ℝ → ℝ → ℝ → Network n m → Vec n → Vec m → Vec n)
noncomputable def _ThesisExactChecks.target_336 : _ThesisExpectedTypes.type_336 := by exact @Thesis.RoutingSupport.sourceLRP
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingSupport.sourceLRP
  let expected ← getConstInfo `_ThesisExactChecks.target_336
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingSupport.sourceLRP"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingSupport.sourceLRP | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingSupport do
    throwError "Defining module mismatch: Thesis.RoutingSupport.sourceLRP"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_336) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingSupport.sourceLRP: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingSupport.sourceLRP"
#check @Thesis.RoutingSupport.sourceLRP
#print axioms _ThesisExactChecks.target_336

section
open HiddenMonotonicity Thesis.Games
open scoped BigOperators
def _ThesisExpectedTypes.type_337 := (∀ {S : Type}, (n : ℕ) → (ℕ → S → S → ℝ) → S → Paths S n → ℝ)
noncomputable def _ThesisExactChecks.target_337 : _ThesisExpectedTypes.type_337 := by exact @Thesis.Games.pathLaw
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.pathLaw
  let expected ← getConstInfo `_ThesisExactChecks.target_337
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Games.pathLaw"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.pathLaw | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.pathLaw"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_337) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.pathLaw: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.pathLaw"
#check @Thesis.Games.pathLaw
#print axioms _ThesisExactChecks.target_337

section
open HiddenMonotonicity Thesis.Games
open scoped BigOperators
def _ThesisExpectedTypes.type_338 := (∀ {S : Type} [Fintype S], ℕ → (ℕ → S → S → ℝ) → (S → ℝ) → S → ℝ)
noncomputable def _ThesisExactChecks.target_338 : _ThesisExpectedTypes.type_338 := by exact @Thesis.Games.backwardDP
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.backwardDP
  let expected ← getConstInfo `_ThesisExactChecks.target_338
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Games.backwardDP"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.backwardDP | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.backwardDP"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_338) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.backwardDP: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.backwardDP"
#check @Thesis.Games.backwardDP
#print axioms _ThesisExactChecks.target_338

section
universe u
open HiddenMonotonicity Thesis.Games
open scoped BigOperators
def _ThesisExpectedTypes.type_339 := (∀ {S : Type u} [Fintype S], (S → ℝ) → (S → ℝ) → ℝ)
noncomputable def _ThesisExactChecks.target_339 : _ThesisExpectedTypes.type_339.{u} := by exact @Thesis.Games.overlap.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.overlap
  let expected ← getConstInfo `_ThesisExactChecks.target_339
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Games.overlap"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.overlap | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.overlap"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_339) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.overlap: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.overlap"
#check @Thesis.Games.overlap
#print axioms _ThesisExactChecks.target_339

section
open HiddenMonotonicity Thesis.Tropical
open scoped BigOperators
def _ThesisExpectedTypes.type_340 := (∀ {I : Type} [Fintype I], Polynomial I → (I → ℝ) → ℝ)
noncomputable def _ThesisExactChecks.target_340 : _ThesisExpectedTypes.type_340 := by exact @Thesis.Tropical.Polynomial.eval
end
run_cmd do
  let target ← getConstInfo `Thesis.Tropical.Polynomial.eval
  let expected ← getConstInfo `_ThesisExactChecks.target_340
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Tropical.Polynomial.eval"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Tropical.Polynomial.eval | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Tropical do
    throwError "Defining module mismatch: Thesis.Tropical.Polynomial.eval"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_340) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Tropical.Polynomial.eval: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Tropical.Polynomial.eval"
#check @Thesis.Tropical.Polynomial.eval
#print axioms _ThesisExactChecks.target_340

section
open HiddenMonotonicity Thesis.Tropical
open scoped BigOperators
def _ThesisExpectedTypes.type_341 := (∀ {I : Type}, Polynomial I → Set (I → ℝ))
noncomputable def _ThesisExactChecks.target_341 : _ThesisExpectedTypes.type_341 := by exact @Thesis.Tropical.Polynomial.newton
end
run_cmd do
  let target ← getConstInfo `Thesis.Tropical.Polynomial.newton
  let expected ← getConstInfo `_ThesisExactChecks.target_341
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Tropical.Polynomial.newton"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Tropical.Polynomial.newton | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Tropical do
    throwError "Defining module mismatch: Thesis.Tropical.Polynomial.newton"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_341) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Tropical.Polynomial.newton: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Tropical.Polynomial.newton"
#check @Thesis.Tropical.Polynomial.newton
#print axioms _ThesisExactChecks.target_341

section
open HiddenMonotonicity Thesis.Tropical
open scoped BigOperators
def _ThesisExpectedTypes.type_342 := (∀ {I : Type} [Fintype I], Set (I → ℝ) → (I → ℝ) → ℝ)
noncomputable def _ThesisExactChecks.target_342 : _ThesisExpectedTypes.type_342 := by exact @Thesis.Tropical.support
end
run_cmd do
  let target ← getConstInfo `Thesis.Tropical.support
  let expected ← getConstInfo `_ThesisExactChecks.target_342
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Tropical.support"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Tropical.support | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Tropical do
    throwError "Defining module mismatch: Thesis.Tropical.support"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_342) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Tropical.support: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Tropical.support"
#check @Thesis.Tropical.support
#print axioms _ThesisExactChecks.target_342

section
open HiddenMonotonicity Thesis.StoppingDAG
open scoped BigOperators
def _ThesisExpectedTypes.type_343 := (∀ {d n : ℕ} (c : Circuit d n), PairVec d → Fin n → Thesis.StoppingDAG.DAGPaths c → ℝ)
noncomputable def _ThesisExactChecks.target_343 : _ThesisExpectedTypes.type_343 := by exact @Thesis.StoppingDAG.pathProbability
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.pathProbability
  let expected ← getConstInfo `_ThesisExactChecks.target_343
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.pathProbability"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.pathProbability | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPaths do
    throwError "Defining module mismatch: Thesis.StoppingDAG.pathProbability"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_343) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.pathProbability: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.pathProbability"
#check @Thesis.StoppingDAG.pathProbability
#print axioms _ThesisExactChecks.target_343

section
open HiddenMonotonicity Thesis.StoppingDAG
open scoped BigOperators
def _ThesisExpectedTypes.type_344 := (∀ {d n : ℕ}, Circuit d n → PairVec d → Fin n → Bool → ℕ → Bool → ℝ)
noncomputable def _ThesisExactChecks.target_344 : _ThesisExpectedTypes.type_344 := by exact @Thesis.StoppingDAG.fullOccupation
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.fullOccupation
  let expected ← getConstInfo `_ThesisExactChecks.target_344
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.fullOccupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.fullOccupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGVisits do
    throwError "Defining module mismatch: Thesis.StoppingDAG.fullOccupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_344) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.fullOccupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.fullOccupation"
#check @Thesis.StoppingDAG.fullOccupation
#print axioms _ThesisExactChecks.target_344

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_345 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (x : Vec d),
 graphWith relu c plan x = c.eval x)
theorem _ThesisExactChecks.target_345 : _ThesisExpectedTypes.type_345 := by exact @Thesis.SoftplusCircuit.graphWith_relu
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.graphWith_relu
  let expected ← getConstInfo `_ThesisExactChecks.target_345
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.graphWith_relu"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.graphWith_relu | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitModel do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.graphWith_relu"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_345) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.graphWith_relu: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.graphWith_relu"
#check @Thesis.SoftplusCircuit.graphWith_relu
#print axioms _ThesisExactChecks.target_345

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_346 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ) (x : PairVec d),
 (graphSplit θ c plan x).1 - (graphSplit θ c plan x).2 = graphSoft θ c plan (x.1-x.2))
theorem _ThesisExactChecks.target_346 : _ThesisExpectedTypes.type_346 := by exact @Thesis.SoftplusCircuit.graphSplit_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.graphSplit_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_346
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.graphSplit_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.graphSplit_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitModel do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.graphSplit_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_346) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.graphSplit_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.graphSplit_recovery"
#check @Thesis.SoftplusCircuit.graphSplit_recovery
#print axioms _ThesisExactChecks.target_346

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_347 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ)
 (x : Vec d) (plus minus : Strategy c plan),
 signedValue θ c plan plus (canonicalStrategy θ c plan x) (x,-x) ≤
   (graphSoft θ c plan x,-graphSoft θ c plan x) ∧
 signedValue θ c plan (canonicalStrategy θ c plan x) (canonicalStrategy θ c plan x) (x,-x) =
   (graphSoft θ c plan x,-graphSoft θ c plan x) ∧
 (graphSoft θ c plan x,-graphSoft θ c plan x) ≤
   signedValue θ c plan (canonicalStrategy θ c plan x) minus (x,-x))
theorem _ThesisExactChecks.target_347 : _ThesisExpectedTypes.type_347 := by exact @Thesis.SoftplusCircuit.graph_saddle
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.graph_saddle
  let expected ← getConstInfo `_ThesisExactChecks.target_347
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.graph_saddle"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.graph_saddle | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitEquilibrium do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.graph_saddle"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_347) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.graph_saddle: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.graph_saddle"
#check @Thesis.SoftplusCircuit.graph_saddle
#print axioms _ThesisExactChecks.target_347

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_348 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ) (x : Vec d),
 SubgamePerfect θ c plan (canonicalStrategy θ c plan x) (canonicalStrategy θ c plan x) (x,-x))
theorem _ThesisExactChecks.target_348 : _ThesisExpectedTypes.type_348 := by exact @Thesis.SoftplusCircuit.canonical_spne
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.canonical_spne
  let expected ← getConstInfo `_ThesisExactChecks.target_348
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.canonical_spne"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.canonical_spne | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitEquilibrium do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.canonical_spne"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_348) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.canonical_spne: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.canonical_spne"
#check @Thesis.SoftplusCircuit.canonical_spne
#print axioms _ThesisExactChecks.target_348

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_349 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ)
 (plus minus : Strategy c plan) (v : Thesis.SoftplusGame.PlayerValues d),
 Thesis.SoftplusGame.advantage (playerValue θ c plan plus minus v) =
 signedValue θ c plan plus minus (Thesis.SoftplusGame.advantage v))
theorem _ThesisExactChecks.target_349 : _ThesisExpectedTypes.type_349 := by exact @Thesis.SoftplusCircuit.playerValue_advantage
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.playerValue_advantage
  let expected ← getConstInfo `_ThesisExactChecks.target_349
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.playerValue_advantage"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.playerValue_advantage | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitPlayers do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.playerValue_advantage"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_349) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.playerValue_advantage: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.playerValue_advantage"
#check @Thesis.SoftplusCircuit.playerValue_advantage
#print axioms _ThesisExactChecks.target_349

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_350 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ) (x : PairVec d),
 playerValue θ c plan (canonicalStrategy θ c plan (x.1-x.2))
   (canonicalStrategy θ c plan (x.1-x.2)) (Thesis.SoftplusGame.pairValues x) =
 Thesis.SoftplusGame.pairValues (graphSplit θ c plan x))
theorem _ThesisExactChecks.target_350 : _ThesisExpectedTypes.type_350 := by exact @Thesis.SoftplusCircuit.playerValue_canonical
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.playerValue_canonical
  let expected ← getConstInfo `_ThesisExactChecks.target_350
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.playerValue_canonical"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.playerValue_canonical | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitPlayers do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.playerValue_canonical"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_350) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.playerValue_canonical: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.playerValue_canonical"
#check @Thesis.SoftplusCircuit.playerValue_canonical
#print axioms _ThesisExactChecks.target_350

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_351 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ)
 (hc : NoPools c plan) (x : Vec d) (plus minus : Strategy c plan),
 SubgamePerfect θ c plan plus minus (x,-x) ↔
 plus=canonicalStrategy θ c plan x ∧ minus=canonicalStrategy θ c plan x)
theorem _ThesisExactChecks.target_351 : _ThesisExpectedTypes.type_351 := by exact @Thesis.SoftplusCircuit.subgamePerfect_iff
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.subgamePerfect_iff
  let expected ← getConstInfo `_ThesisExactChecks.target_351
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.subgamePerfect_iff"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.subgamePerfect_iff | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitUniqueness do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.subgamePerfect_iff"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_351) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.subgamePerfect_iff: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.subgamePerfect_iff"
#check @Thesis.SoftplusCircuit.subgamePerfect_iff
#print axioms _ThesisExactChecks.target_351

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_352 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ) (x : PairVec d),
 SubgamePerfect θ c plan (canonicalStrategy θ c plan (x.1-x.2))
   (canonicalStrategy θ c plan (x.1-x.2)) (x.1-x.2,-(x.1-x.2)) ∧
 playerValue θ c plan (canonicalStrategy θ c plan (x.1-x.2))
   (canonicalStrategy θ c plan (x.1-x.2)) (Thesis.SoftplusGame.pairValues x) =
   Thesis.SoftplusGame.pairValues (graphSplit θ c plan x) ∧
 (graphSplit θ c plan x).1-(graphSplit θ c plan x).2=graphSoft θ c plan (x.1-x.2))
theorem _ThesisExactChecks.target_352 : _ThesisExpectedTypes.type_352 := by exact @Thesis.SoftplusCircuit.softplus_forward_spne
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.softplus_forward_spne
  let expected ← getConstInfo `_ThesisExactChecks.target_352
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.softplus_forward_spne"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.softplus_forward_spne | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitUniqueness do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.softplus_forward_spne"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_352) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.softplus_forward_spne: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.softplus_forward_spne"
#check @Thesis.SoftplusCircuit.softplus_forward_spne
#print axioms _ThesisExactChecks.target_352

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_353 : Prop := (∀ {n : ℕ} {e : SignedExpr (Fin n)} (θ : ℝ) (spec : NodeSpec e) (x : Vec n),
 (∑ target : Option (Fin n × Bool), nodeProbability θ spec x target) = 1)
theorem _ThesisExactChecks.target_353 : _ThesisExpectedTypes.type_353 := by exact @Thesis.SoftplusCircuit.nodeProbability_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.nodeProbability_normalized
  let expected ← getConstInfo `_ThesisExactChecks.target_353
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.nodeProbability_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.nodeProbability_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitRows do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.nodeProbability_normalized"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_353) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.nodeProbability_normalized: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.nodeProbability_normalized"
#check @Thesis.SoftplusCircuit.nodeProbability_normalized
#print axioms _ThesisExactChecks.target_353

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_354 : Prop := (∀ {n : ℕ} {e : SignedExpr (Fin n)} (θ : ℝ) (spec : NodeSpec e) (x : Vec n)
 (i : Fin n) (b : Bool), nodeDiscount spec x * nodeProbability θ spec x (some (i,b)) =
 if b then (selectedWeights θ spec x).2 i else (selectedWeights θ spec x).1 i)
theorem _ThesisExactChecks.target_354 : _ThesisExpectedTypes.type_354 := by exact @Thesis.SoftplusCircuit.node_discount_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.node_discount_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_354
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.node_discount_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.node_discount_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitRows do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.node_discount_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_354) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.node_discount_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.node_discount_recovery"
#check @Thesis.SoftplusCircuit.node_discount_recovery
#print axioms _ThesisExactChecks.target_354

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_355 : Prop := (∀ {n : ℕ} {e : SignedExpr (Fin n)} (θ : ℝ) (spec : NodeSpec e) (x : Vec n)
 (v : Thesis.SoftplusGame.PlayerValues n) (player turn : Bool),
 nodePlayer θ spec (canonicalNode θ spec x) (canonicalNode θ spec x) v player turn =
 nodeReward θ spec x player turn +
 ∑ i : Fin n, ∑ b : Bool, nodeDiscount spec x * nodeProbability θ spec x (some (i,b)) *
 v player (Bool.xor turn b) i)
theorem _ThesisExactChecks.target_355 : _ThesisExpectedTypes.type_355 := by exact @Thesis.SoftplusCircuit.nodePlayer_transition
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.nodePlayer_transition
  let expected ← getConstInfo `_ThesisExactChecks.target_355
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.nodePlayer_transition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.nodePlayer_transition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitTransition do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.nodePlayer_transition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_355) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.nodePlayer_transition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.nodePlayer_transition"
#check @Thesis.SoftplusCircuit.nodePlayer_transition
#print axioms _ThesisExactChecks.target_355

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_356 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ)
 (x : Vec d) (hx : Regular θ c plan x),
 HasFDerivAt (graphSoft θ c plan)
 (matrixCLM ((graphKernel θ c plan x).1-(graphKernel θ c plan x).2)) x)
theorem _ThesisExactChecks.target_356 : _ThesisExpectedTypes.type_356 := by exact @Thesis.SoftplusCircuit.graphSoft_hasFDerivAt
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.graphSoft_hasFDerivAt
  let expected ← getConstInfo `_ThesisExactChecks.target_356
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.graphSoft_hasFDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.graphSoft_hasFDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitDerivative do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.graphSoft_hasFDerivAt"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_356) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.graphSoft_hasFDerivAt: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.graphSoft_hasFDerivAt"
#check @Thesis.SoftplusCircuit.graphSoft_hasFDerivAt
#print axioms _ThesisExactChecks.target_356

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_357 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d) (j : Fin n),
 (∑ path : Thesis.StoppingDAG.DAGPaths c, pathProbability θ c plan x j path) = 1)
theorem _ThesisExactChecks.target_357 : _ThesisExpectedTypes.type_357 := by exact @Thesis.SoftplusCircuit.pathProbability_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.pathProbability_normalized
  let expected ← getConstInfo `_ThesisExactChecks.target_357
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.pathProbability_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.pathProbability_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitPaths do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.pathProbability_normalized"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_357) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.pathProbability_normalized: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.pathProbability_normalized"
#check @Thesis.SoftplusCircuit.pathProbability_normalized
#print axioms _ThesisExactChecks.target_357

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_358 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d)
 (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool),
 occupation c plan θ x j turn i channel =
 if Bool.xor channel turn then (graphKernel θ c plan x).2 j i else (graphKernel θ c plan x).1 j i)
theorem _ThesisExactChecks.target_358 : _ThesisExpectedTypes.type_358 := by exact @Thesis.SoftplusCircuit.occupation_eq_kernel
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.occupation_eq_kernel
  let expected ← getConstInfo `_ThesisExactChecks.target_358
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.occupation_eq_kernel"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.occupation_eq_kernel | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitOccupation do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.occupation_eq_kernel"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_358) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.occupation_eq_kernel: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.occupation_eq_kernel"
#check @Thesis.SoftplusCircuit.occupation_eq_kernel
#print axioms _ThesisExactChecks.target_358

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_359 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ)
 (x : Vec d) (hx : Regular θ c plan x) (j : Fin n) (i : Fin d),
 (fderiv ℝ (graphSoft θ c plan) x (Pi.single i 1)) j =
 occupation c plan θ x j false i false - occupation c plan θ x j false i true)
theorem _ThesisExactChecks.target_359 : _ThesisExpectedTypes.type_359 := by exact @Thesis.SoftplusCircuit.graph_derivative_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.graph_derivative_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_359
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.graph_derivative_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.graph_derivative_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitOccupation do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.graph_derivative_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_359) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.graph_derivative_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.graph_derivative_occupation"
#check @Thesis.SoftplusCircuit.graph_derivative_occupation
#print axioms _ThesisExactChecks.target_359

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_360 : Prop := (∀ {d m n : ℕ} (pre : Circuit d m) (prePlan : Plan pre)
 (suffix : Circuit m n) (suffixPlan : Plan suffix) (θ : ℝ) (x : Vec d),
 graphSoft θ (Thesis.StoppingDAG.graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) x =
 graphSoft θ suffix suffixPlan (graphSoft θ pre prePlan x))
theorem _ThesisExactChecks.target_360 : _ThesisExpectedTypes.type_360 := by exact @Thesis.SoftplusCircuit.graft_soft
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.graft_soft
  let expected ← getConstInfo `_ThesisExactChecks.target_360
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.graft_soft"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.graft_soft | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitCuts do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.graft_soft"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_360) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.graft_soft: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.graft_soft"
#check @Thesis.SoftplusCircuit.graft_soft
#print axioms _ThesisExactChecks.target_360

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_361 : Prop := (∀ {d m n : ℕ} (pre : Circuit d (m+1)) (prePlan : Plan pre)
 (suffix : Circuit (m+1) n) (suffixPlan : Plan suffix) (θ : ℝ) (x : Vec d)
 (j : Fin n) (turn channel : Bool),
 fullOccupation (Thesis.StoppingDAG.graft pre suffix) (graftPlan pre prePlan suffix suffixPlan)
   θ x j turn m channel =
 occupation suffix suffixPlan θ (graphSoft θ pre prePlan x) j turn (Fin.last m) channel)
theorem _ThesisExactChecks.target_361 : _ThesisExpectedTypes.type_361 := by exact @Thesis.SoftplusCircuit.fullOccupation_graft_last
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.fullOccupation_graft_last
  let expected ← getConstInfo `_ThesisExactChecks.target_361
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.fullOccupation_graft_last"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.fullOccupation_graft_last | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitVisits do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.fullOccupation_graft_last"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_361) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.fullOccupation_graft_last: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.fullOccupation_graft_last"
#check @Thesis.SoftplusCircuit.fullOccupation_graft_last
#print axioms _ThesisExactChecks.target_361

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_362 : Prop := (∀ {d m n : ℕ} (pre : Circuit d (m+1)) (prePlan : Plan pre)
 (suffix : Circuit (m+1) n) (suffixPlan : Plan suffix) (θ : ℝ) (hθ : 0 < θ) (x : Vec d)
 (hx : Regular θ (Thesis.StoppingDAG.graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) x)
 (j : Fin n) (q : Bool),
 (fderiv ℝ (graphSoft θ suffix suffixPlan) (graphSoft θ pre prePlan x) (Pi.single (Fin.last m) 1)) j =
 (if q then (-1 : ℝ) else 1) *
 (fullOccupation (Thesis.StoppingDAG.graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) θ x j q m false -
  fullOccupation (Thesis.StoppingDAG.graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) θ x j q m true))
theorem _ThesisExactChecks.target_362 : _ThesisExpectedTypes.type_362 := by exact @Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation
  let expected ← getConstInfo `_ThesisExactChecks.target_362
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitVisits do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_362) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation"
#check @Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation
#print axioms _ThesisExactChecks.target_362

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_363 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d)
 (v : Thesis.SoftplusGame.PlayerValues d) (player : Bool) (j : Fin n) (turn : Bool),
 expectedPayoff c plan θ x v player j turn =
 playerValue θ c plan (canonicalStrategy θ c plan x) (canonicalStrategy θ c plan x) v player turn j)
theorem _ThesisExactChecks.target_363 : _ThesisExpectedTypes.type_363 := by exact @Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue
  let expected ← getConstInfo `_ThesisExactChecks.target_363
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitPayoff do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_363) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue"
#check @Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue
#print axioms _ThesisExactChecks.target_363

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_364 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ)
 (x : PairVec d) (player turn : Bool) (j : Fin n),
 expectedPayoff c plan θ (x.1-x.2) (Thesis.SoftplusGame.pairValues x) player j turn =
 if player=turn then (graphSplit θ c plan x).1 j else (graphSplit θ c plan x).2 j)
theorem _ThesisExactChecks.target_364 : _ThesisExpectedTypes.type_364 := by exact @Thesis.SoftplusCircuit.expectedPayoff_eq_split
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.expectedPayoff_eq_split
  let expected ← getConstInfo `_ThesisExactChecks.target_364
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.expectedPayoff_eq_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.expectedPayoff_eq_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitPayoff do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.expectedPayoff_eq_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_364) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.expectedPayoff_eq_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.expectedPayoff_eq_split"
#check @Thesis.SoftplusCircuit.expectedPayoff_eq_split
#print axioms _ThesisExactChecks.target_364

section
open Thesis.Games Thesis.ConditionedSurvival Thesis.Randomization
open scoped BigOperators
def _ThesisExpectedTypes.type_365 : Prop := (∀ {S : Type} [Fintype S] (N i : ℕ) (hi : i ≤ N)
(K : ℕ → S → S → ℝ) (s t : S),
timeMass N i K s t = prefixMass i K s t * survival N K i t)
theorem _ThesisExactChecks.target_365 : _ThesisExpectedTypes.type_365 := by exact @Thesis.ConditionedSurvival.timeMass_factorization
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.timeMass_factorization
  let expected ← getConstInfo `_ThesisExactChecks.target_365
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.timeMass_factorization"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.timeMass_factorization | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedTrajectory do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.timeMass_factorization"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_365) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.timeMass_factorization: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.timeMass_factorization"
#check @Thesis.ConditionedSurvival.timeMass_factorization
#print axioms _ThesisExactChecks.target_365

section
open Thesis.Games Thesis.ConditionedSurvival Thesis.Randomization
open scoped BigOperators
def _ThesisExpectedTypes.type_366 : Prop := (∀ {S : Type} [Fintype S] (N i : ℕ) (hi : i ≤ N)
(K : ℕ → S → S → ℝ) (hK : ∀ j s t, 0 ≤ K j s t)
(s : S) (hs : 0 < survival N K 0 s) (t : S),
timeMass N i (kernel K (survival N K)) s t =
prefixMass i K s t * survival N K i t / survival N K 0 s)
theorem _ThesisExactChecks.target_366 : _ThesisExpectedTypes.type_366 := by exact @Thesis.ConditionedSurvival.conditioned_time_marginal
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.conditioned_time_marginal
  let expected ← getConstInfo `_ThesisExactChecks.target_366
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.conditioned_time_marginal"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.conditioned_time_marginal | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedTrajectory do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.conditioned_time_marginal"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_366) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.conditioned_time_marginal: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.conditioned_time_marginal"
#check @Thesis.ConditionedSurvival.conditioned_time_marginal
#print axioms _ThesisExactChecks.target_366

section
open Thesis.Games Thesis.ConditionedSurvival Thesis.Randomization
open scoped BigOperators
def _ThesisExpectedTypes.type_367 : Prop := (∀ {S : Type} [Fintype S] (N : ℕ) (A B : ℕ → S → S → ℝ)
(hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
(i : ℕ) (s t : S),
Real.sqrt (kernel A (survival N A) i s t * kernel B (survival N B) i s t) =
Real.sqrt (A i s t * B i s t) *
Real.sqrt (survival N A (i+1) t * survival N B (i+1) t) /
Real.sqrt (survival N A i s * survival N B i s))
theorem _ThesisExactChecks.target_367 : _ThesisExpectedTypes.type_367 := by exact @Thesis.ConditionedSurvival.conditioned_geometric_kernel
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.conditioned_geometric_kernel
  let expected ← getConstInfo `_ThesisExactChecks.target_367
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.conditioned_geometric_kernel"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.conditioned_geometric_kernel | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedTrajectory do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.conditioned_geometric_kernel"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_367) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.conditioned_geometric_kernel: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.conditioned_geometric_kernel"
#check @Thesis.ConditionedSurvival.conditioned_geometric_kernel
#print axioms _ThesisExactChecks.target_367

section
open Thesis.Games Thesis.ConditionedSurvival Thesis.Randomization
open scoped BigOperators
def _ThesisExpectedTypes.type_368 : Prop := (∀ {S : Type} [Fintype S] (N : ℕ) (A B : ℕ → S → S → ℝ)
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
1 - ordinaryOverlap N A B s / Real.sqrt (survival N A 0 s * survival N B 0 s)))
theorem _ThesisExactChecks.target_368 : _ThesisExpectedTypes.type_368 := by exact @Thesis.ConditionedSurvival.conditioned_survival_statistics
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.conditioned_survival_statistics
  let expected ← getConstInfo `_ThesisExactChecks.target_368
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.conditioned_survival_statistics"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.conditioned_survival_statistics | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedTrajectory do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.conditioned_survival_statistics"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_368) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.conditioned_survival_statistics: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.conditioned_survival_statistics"
#check @Thesis.ConditionedSurvival.conditioned_survival_statistics
#print axioms _ThesisExactChecks.target_368

section
open Thesis.Games Thesis.ConditionedSurvival Thesis.Randomization
open scoped BigOperators
def _ThesisExpectedTypes.type_369 : Prop := (∀ {S : Type} [Fintype S] (A B : ℕ → S → S → ℝ)
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
backwardDP n (fun i u v => Real.sqrt (A i u v * B i u v)) (fun _ => 1) s))
theorem _ThesisExactChecks.target_369 : _ThesisExpectedTypes.type_369 := by exact @Thesis.ConditionedSurvival.trajectory_bc_monotone
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.trajectory_bc_monotone
  let expected ← getConstInfo `_ThesisExactChecks.target_369
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.trajectory_bc_monotone"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.trajectory_bc_monotone | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedTrajectory do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.trajectory_bc_monotone"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_369) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.trajectory_bc_monotone: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.trajectory_bc_monotone"
#check @Thesis.ConditionedSurvival.trajectory_bc_monotone
#print axioms _ThesisExactChecks.target_369

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_370 : Prop := (∀ (C : ℝ → ℝ) (L : ℝ), ConvexOn ℝ Set.univ (asymmetricLift C L) ↔ ConvexOn ℝ Set.univ C)
theorem _ThesisExactChecks.target_370 : _ThesisExpectedTypes.type_370 := by exact @HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff
  let expected ← getConstInfo `_ThesisExactChecks.target_370
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_370) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff"
#check @HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff
#print axioms _ThesisExactChecks.target_370

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_371 : Prop := (∀ (C : ℝ → ℝ) (L : ℝ), Monotone (asymmetricLift C L) ↔ ∀ a b : ℝ, a ≤ b → 0 ≤ C b - C a ∧ C b - C a ≤ L * (b - a))
theorem _ThesisExactChecks.target_371 : _ThesisExpectedTypes.type_371 := by exact @HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments
  let expected ← getConstInfo `_ThesisExactChecks.target_371
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_371) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments"
#check @HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments
#print axioms _ThesisExactChecks.target_371

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_372 : Prop := (∀ (C D : ℝ → ℝ) (hC : ∀ x : ℝ, HasDerivAt C (D x) x) (L : ℝ), Monotone (asymmetricLift C L) ↔ ∀ x : ℝ, 0 ≤ D x ∧ D x ≤ L)
theorem _ThesisExactChecks.target_372 : _ThesisExpectedTypes.type_372 := by exact @HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff
  let expected ← getConstInfo `_ThesisExactChecks.target_372
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_372) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff"
#check @HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff
#print axioms _ThesisExactChecks.target_372

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_373 : Prop := (∀ (P Q f : ℝ → ℝ) (L : ℝ) (hP : ConvexOn ℝ Set.univ P) (hQ : ConvexOn ℝ Set.univ Q) (hPd : ∀ a b : ℝ, a ≤ b → 0 ≤ P b - P a ∧ P b - P a ≤ L * (b - a)) (hQd : ∀ a b : ℝ, a ≤ b → 0 ≤ Q b - Q a ∧ Q b - Q a ≤ L * (b - a)) (hdiff : ∀ t : ℝ, P t - Q t = f t), ConvexOn ℝ Set.univ (asymmetricLift P L) ∧ ConvexOn ℝ Set.univ (asymmetricLift Q L) ∧ Monotone (asymmetricLift P L) ∧ Monotone (asymmetricLift Q L) ∧ ∀ z : ℝ × ℝ, asymmetricLift P L z - asymmetricLift Q L z = f (z.1 - z.2))
theorem _ThesisExactChecks.target_373 : _ThesisExpectedTypes.type_373 := by exact @HiddenMonotonicity.SmoothDC.asymmetric_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.asymmetric_split
  let expected ← getConstInfo `_ThesisExactChecks.target_373
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.asymmetric_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.asymmetric_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.asymmetric_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_373) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.asymmetric_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.asymmetric_split"
#check @HiddenMonotonicity.SmoothDC.asymmetric_split
#print axioms _ThesisExactChecks.target_373

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_374 : Prop := (∀ (C : ℝ → ℝ) (L x y c : ℝ), asymmetricLift C L (x + c, y + c) = asymmetricLift C L (x, y) + L * c)
theorem _ThesisExactChecks.target_374 : _ThesisExpectedTypes.type_374 := by exact @HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift
  let expected ← getConstInfo `_ThesisExactChecks.target_374
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_374) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift"
#check @HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift
#print axioms _ThesisExactChecks.target_374

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_375 : Prop := (∀ z : ℝ × ℝ, asymmetricLift relu 1 z = max z.1 z.2 ∧ asymmetricLift (fun _ : ℝ => 0) 1 z = z.2)
theorem _ThesisExactChecks.target_375 : _ThesisExpectedTypes.type_375 := by exact @HiddenMonotonicity.SmoothDC.asymmetricLift_relu
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.asymmetricLift_relu
  let expected ← getConstInfo `_ThesisExactChecks.target_375
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_relu"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.asymmetricLift_relu | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_relu"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_375) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.asymmetricLift_relu: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_relu"
#check @HiddenMonotonicity.SmoothDC.asymmetricLift_relu
#print axioms _ThesisExactChecks.target_375

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_376 : Prop := (ConvexOn ℝ Set.univ (asymmetricLift relu 1) ∧ ConvexOn ℝ Set.univ (asymmetricLift (fun _ : ℝ => 0) 1) ∧ Monotone (asymmetricLift relu 1) ∧ Monotone (asymmetricLift (fun _ : ℝ => 0) 1) ∧ ∀ z : ℝ × ℝ, asymmetricLift relu 1 z - asymmetricLift (fun _ : ℝ => 0) 1 z = relu (z.1 - z.2))
theorem _ThesisExactChecks.target_376 : _ThesisExpectedTypes.type_376 := by exact @HiddenMonotonicity.SmoothDC.relu_asymmetric_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.relu_asymmetric_split
  let expected ← getConstInfo `_ThesisExactChecks.target_376
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.relu_asymmetric_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.relu_asymmetric_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.relu_asymmetric_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_376) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.relu_asymmetric_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.relu_asymmetric_split"
#check @HiddenMonotonicity.SmoothDC.relu_asymmetric_split
#print axioms _ThesisExactChecks.target_376

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC MeasureTheory
def _ThesisExpectedTypes.type_377 : Prop := (∀ (f : ℝ → ℝ) (x : ℝ), positiveCurvature f x = (|curvature f x| + curvature f x) / 2)
theorem _ThesisExactChecks.target_377 : _ThesisExpectedTypes.type_377 := by exact @HiddenMonotonicity.SmoothDC.positiveCurvature_eq_absolute
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.positiveCurvature_eq_absolute
  let expected ← getConstInfo `_ThesisExactChecks.target_377
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.positiveCurvature_eq_absolute"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.positiveCurvature_eq_absolute | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.CurvatureMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.positiveCurvature_eq_absolute"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_377) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.positiveCurvature_eq_absolute: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.positiveCurvature_eq_absolute"
#check @HiddenMonotonicity.SmoothDC.positiveCurvature_eq_absolute
#print axioms _ThesisExactChecks.target_377

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC MeasureTheory
def _ThesisExpectedTypes.type_378 : Prop := (∀ (f : ℝ → ℝ) (x : ℝ), negativeCurvature f x = (|curvature f x| - curvature f x) / 2)
theorem _ThesisExactChecks.target_378 : _ThesisExpectedTypes.type_378 := by exact @HiddenMonotonicity.SmoothDC.negativeCurvature_eq_absolute
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.negativeCurvature_eq_absolute
  let expected ← getConstInfo `_ThesisExactChecks.target_378
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.negativeCurvature_eq_absolute"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.negativeCurvature_eq_absolute | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.CurvatureMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.negativeCurvature_eq_absolute"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_378) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.negativeCurvature_eq_absolute: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.negativeCurvature_eq_absolute"
#check @HiddenMonotonicity.SmoothDC.negativeCurvature_eq_absolute
#print axioms _ThesisExactChecks.target_378

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC MeasureTheory
def _ThesisExpectedTypes.type_379 : Prop := (∀ (f : ℝ → ℝ) (hq : Integrable (curvature f)), totalPositiveCurvature f + totalNegativeCurvature f = ∫ t, |curvature f t|)
theorem _ThesisExactChecks.target_379 : _ThesisExpectedTypes.type_379 := by exact @HiddenMonotonicity.SmoothDC.total_curvature_eq_absolute
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.total_curvature_eq_absolute
  let expected ← getConstInfo `_ThesisExactChecks.target_379
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.total_curvature_eq_absolute"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.total_curvature_eq_absolute | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.CurvatureMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.total_curvature_eq_absolute"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_379) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.total_curvature_eq_absolute: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.total_curvature_eq_absolute"
#check @HiddenMonotonicity.SmoothDC.total_curvature_eq_absolute
#print axioms _ThesisExactChecks.target_379

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC MeasureTheory
def _ThesisExpectedTypes.type_380 : Prop := (∀ (f : ℝ → ℝ) (hq : Integrable (curvature f)) (x : ℝ), (0 ≤ D1 f x + curvatureSlopeShift f ∧ D1 f x + curvatureSlopeShift f ≤ curvatureLiftWidth f) ∧ (0 ≤ D2 f x + curvatureSlopeShift f ∧ D2 f x + curvatureSlopeShift f ≤ curvatureLiftWidth f))
theorem _ThesisExactChecks.target_380 : _ThesisExpectedTypes.type_380 := by exact @HiddenMonotonicity.SmoothDC.curvature_profile_slope_bounds
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.curvature_profile_slope_bounds
  let expected ← getConstInfo `_ThesisExactChecks.target_380
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.curvature_profile_slope_bounds"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.curvature_profile_slope_bounds | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.CurvatureMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.curvature_profile_slope_bounds"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_380) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.curvature_profile_slope_bounds: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.curvature_profile_slope_bounds"
#check @HiddenMonotonicity.SmoothDC.curvature_profile_slope_bounds
#print axioms _ThesisExactChecks.target_380

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC MeasureTheory
def _ThesisExpectedTypes.type_381 : Prop := (∀ (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (deriv f) a b) (hq : Integrable (curvature f)) (x : ℝ), curvaturePositiveProfile f x - curvatureNegativeProfile f x = f x)
theorem _ThesisExactChecks.target_381 : _ThesisExpectedTypes.type_381 := by exact @HiddenMonotonicity.SmoothDC.curvature_profile_difference
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.curvature_profile_difference
  let expected ← getConstInfo `_ThesisExactChecks.target_381
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.curvature_profile_difference"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.curvature_profile_difference | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.CurvatureMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.curvature_profile_difference"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_381) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.curvature_profile_difference: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.curvature_profile_difference"
#check @HiddenMonotonicity.SmoothDC.curvature_profile_difference
#print axioms _ThesisExactChecks.target_381

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC MeasureTheory
def _ThesisExpectedTypes.type_382 : Prop := (∀ (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (deriv f) a b) (hq : Integrable (curvature f)), ConvexOn ℝ Set.univ (fun z => (curvatureLiftPair f z).1) ∧ ConvexOn ℝ Set.univ (fun z => (curvatureLiftPair f z).2) ∧ Monotone (fun z => (curvatureLiftPair f z).1) ∧ Monotone (fun z => (curvatureLiftPair f z).2) ∧ ∀ p q : ℝ, (curvatureLiftPair f (p, q)).1 - (curvatureLiftPair f (p, q)).2 = f (p - q))
theorem _ThesisExactChecks.target_382 : _ThesisExpectedTypes.type_382 := by exact @HiddenMonotonicity.SmoothDC.curvature_monotone_dc_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.curvature_monotone_dc_split
  let expected ← getConstInfo `_ThesisExactChecks.target_382
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.curvature_monotone_dc_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.curvature_monotone_dc_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.CurvatureMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.curvature_monotone_dc_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_382) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.curvature_monotone_dc_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.curvature_monotone_dc_split"
#check @HiddenMonotonicity.SmoothDC.curvature_monotone_dc_split
#print axioms _ThesisExactChecks.target_382

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC MeasureTheory
def _ThesisExpectedTypes.type_383 : Prop := (∀ (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (deriv f) a b) (hq : Integrable (curvature f)) (hzero : 0 ≤ f 0), ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → 0 ≤ (curvatureLiftPair f (p, q)).1 ∧ 0 ≤ (curvatureLiftPair f (p, q)).2)
theorem _ThesisExactChecks.target_383 : _ThesisExpectedTypes.type_383 := by exact @HiddenMonotonicity.SmoothDC.curvatureLiftPair_nonnegative
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.curvatureLiftPair_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_383
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.curvatureLiftPair_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.curvatureLiftPair_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.CurvatureMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.curvatureLiftPair_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_383) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.curvatureLiftPair_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.curvatureLiftPair_nonnegative"
#check @HiddenMonotonicity.SmoothDC.curvatureLiftPair_nonnegative
#print axioms _ThesisExactChecks.target_383

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC MeasureTheory
def _ThesisExpectedTypes.type_384 : Prop := (∀ (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (deriv f) a b) (hq : Integrable (curvature f)), ConvexOn ℝ Set.univ (fun z => (normalizedCurvatureLiftPair f z).1) ∧ ConvexOn ℝ Set.univ (fun z => (normalizedCurvatureLiftPair f z).2) ∧ Monotone (fun z => (normalizedCurvatureLiftPair f z).1) ∧ Monotone (fun z => (normalizedCurvatureLiftPair f z).2) ∧ ∀ p q : ℝ, (normalizedCurvatureLiftPair f (p, q)).1 - (normalizedCurvatureLiftPair f (p, q)).2 = f (p - q))
theorem _ThesisExactChecks.target_384 : _ThesisExpectedTypes.type_384 := by exact @HiddenMonotonicity.SmoothDC.normalized_curvature_monotone_dc_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.normalized_curvature_monotone_dc_split
  let expected ← getConstInfo `_ThesisExactChecks.target_384
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.normalized_curvature_monotone_dc_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.normalized_curvature_monotone_dc_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.CurvatureMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.normalized_curvature_monotone_dc_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_384) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.normalized_curvature_monotone_dc_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.normalized_curvature_monotone_dc_split"
#check @HiddenMonotonicity.SmoothDC.normalized_curvature_monotone_dc_split
#print axioms _ThesisExactChecks.target_384

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC MeasureTheory
def _ThesisExpectedTypes.type_385 : Prop := (∀ (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (deriv f) a b) (hq : Integrable (curvature f)), ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → 0 ≤ (normalizedCurvatureLiftPair f (p, q)).1 ∧ 0 ≤ (normalizedCurvatureLiftPair f (p, q)).2)
theorem _ThesisExactChecks.target_385 : _ThesisExpectedTypes.type_385 := by exact @HiddenMonotonicity.SmoothDC.normalizedCurvatureLiftPair_nonnegative
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.normalizedCurvatureLiftPair_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_385
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.normalizedCurvatureLiftPair_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.normalizedCurvatureLiftPair_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.CurvatureMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.normalizedCurvatureLiftPair_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_385) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.normalizedCurvatureLiftPair_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.normalizedCurvatureLiftPair_nonnegative"
#check @HiddenMonotonicity.SmoothDC.normalizedCurvatureLiftPair_nonnegative
#print axioms _ThesisExactChecks.target_385

section
open Set HiddenMonotonicity
def _ThesisExpectedTypes.type_386 : Prop := (∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative) (σ : ℝ → ℝ) (φ : (ℝ × ℝ) → ℝ × ℝ) (hv : ValidPairActivation σ φ) (hm : Monotone φ) (hc : ConvexPairActivation φ), Monotone (net.decomposeWith φ) ∧ (∀ i, ConvexOn ℝ univ (fun x : PairVec n => (net.decomposeWith φ x).1 i)) ∧ (∀ i, ConvexOn ℝ univ (fun x : PairVec n => (net.decomposeWith φ x).2 i)) ∧ ∀ x : PairVec n, (net.decomposeWith φ x).1 - (net.decomposeWith φ x).2 = net.forwardWith σ (x.1 - x.2))
theorem _ThesisExactChecks.target_386 : _ThesisExpectedTypes.type_386 := by exact @HiddenMonotonicity.Network.convex_monotone_decomposition
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.convex_monotone_decomposition
  let expected ← getConstInfo `_ThesisExactChecks.target_386
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.convex_monotone_decomposition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.convex_monotone_decomposition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexMonotoneNetwork do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.convex_monotone_decomposition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_386) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.convex_monotone_decomposition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.convex_monotone_decomposition"
#check @HiddenMonotonicity.Network.convex_monotone_decomposition
#print axioms _ThesisExactChecks.target_386

section
open Set HiddenMonotonicity
def _ThesisExpectedTypes.type_387 : Prop := (∀ {d n m : ℕ} (net : Network n m) (hw : net.Nonnegative) (φ : (ℝ × ℝ) → ℝ × ℝ) (hm : Monotone φ) (hc : ConvexPairActivation φ) (p q : Vec d → Vec n) (hp : ∀ i, ConvexOn ℝ univ (fun x => p x i)) (hq : ∀ i, ConvexOn ℝ univ (fun x => q x i)), (∀ i, ConvexOn ℝ univ (fun x => (net.decomposeWith φ (p x,q x)).1 i)) ∧ (∀ i, ConvexOn ℝ univ (fun x => (net.decomposeWith φ (p x,q x)).2 i)))
theorem _ThesisExactChecks.target_387 : _ThesisExpectedTypes.type_387 := by exact @HiddenMonotonicity.Network.decomposeWith_convex_input
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.decomposeWith_convex_input
  let expected ← getConstInfo `_ThesisExactChecks.target_387
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.decomposeWith_convex_input"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.decomposeWith_convex_input | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexMonotoneNetwork do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.decomposeWith_convex_input"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_387) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.decomposeWith_convex_input: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.decomposeWith_convex_input"
#check @HiddenMonotonicity.Network.decomposeWith_convex_input
#print axioms _ThesisExactChecks.target_387

section
open Set HiddenMonotonicity
def _ThesisExpectedTypes.type_388 : Prop := (∀ {d n : ℕ} (f : PairVec n → ℝ) (hm : Monotone f) (hf : ConvexOn ℝ univ f) (p q : Vec d → Vec n) (hp : ∀ i, ConvexOn ℝ univ (fun x => p x i)) (hq : ∀ i, ConvexOn ℝ univ (fun x => q x i)), ConvexOn ℝ univ (fun x => f (p x,q x)))
theorem _ThesisExactChecks.target_388 : _ThesisExpectedTypes.type_388 := by exact @HiddenMonotonicity.convex_monotone_pair_input
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.convex_monotone_pair_input
  let expected ← getConstInfo `_ThesisExactChecks.target_388
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.convex_monotone_pair_input"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.convex_monotone_pair_input | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexMonotoneNetwork do
    throwError "Defining module mismatch: HiddenMonotonicity.convex_monotone_pair_input"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_388) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.convex_monotone_pair_input: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.convex_monotone_pair_input"
#check @HiddenMonotonicity.convex_monotone_pair_input
#print axioms _ThesisExactChecks.target_388

section
open HiddenMonotonicity
def _ThesisExpectedTypes.type_389 : Prop := (∀ (n m k : ℕ) (backbone : Network n m)
    (activation : ℝ → ℝ) (lift : (ℝ × ℝ) → ℝ × ℝ),
    ValidPairActivation activation lift →
    ∀ (positive negative : Matrix (Fin k) (Fin m) ℝ)
      (positiveBias negativeBias : Vec k) (input : PairVec n),
      (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).1 -
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).2 =
        affineLayer positive negative positiveBias negativeBias
          (backbone.forwardWith activation (input.1 - input.2)))
theorem _ThesisExactChecks.target_389 : _ThesisExpectedTypes.type_389 := by exact @HiddenMonotonicity.Network.affineDecomposeWith_recovery
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affineDecomposeWith_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_389
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affineDecomposeWith_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affineDecomposeWith_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexMonotoneReadout do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affineDecomposeWith_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_389) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affineDecomposeWith_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affineDecomposeWith_recovery"
#check @HiddenMonotonicity.Network.affineDecomposeWith_recovery
#print axioms _ThesisExactChecks.target_389

section
open HiddenMonotonicity
def _ThesisExpectedTypes.type_390 : Prop := (∀ (n m k : ℕ) (backbone : Network n m), backbone.Nonnegative →
    ∀ (activation : ℝ → ℝ) (lift : (ℝ × ℝ) → ℝ × ℝ),
    ValidPairActivation activation lift → Monotone lift →
    (ConvexOn ℝ Set.univ (fun z => (lift z).1) ∧
      ConvexOn ℝ Set.univ (fun z => (lift z).2)) →
    ∀ (positive negative : Matrix (Fin k) (Fin m) ℝ),
      (∀ i j, 0 ≤ positive i j) → (∀ i j, 0 ≤ negative i j) →
    ∀ (positiveBias negativeBias : Vec k),
      Monotone (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : PairVec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).1 j)) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : PairVec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).2 j)) ∧
      ∀ input : PairVec n,
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).1 -
          (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).2 =
          affineLayer positive negative positiveBias negativeBias
            (backbone.forwardWith activation (input.1 - input.2)))
theorem _ThesisExactChecks.target_390 : _ThesisExpectedTypes.type_390 := by exact @HiddenMonotonicity.Network.affine_convex_monotone_decomposition
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_convex_monotone_decomposition
  let expected ← getConstInfo `_ThesisExactChecks.target_390
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_convex_monotone_decomposition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_convex_monotone_decomposition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexMonotoneReadout do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_convex_monotone_decomposition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_390) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_convex_monotone_decomposition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_convex_monotone_decomposition"
#check @HiddenMonotonicity.Network.affine_convex_monotone_decomposition
#print axioms _ThesisExactChecks.target_390

section
open HiddenMonotonicity
def _ThesisExpectedTypes.type_391 : Prop := (∀ (n m k : ℕ) (backbone : Network n m), backbone.Nonnegative →
    ∀ (activation : ℝ → ℝ) (lift : (ℝ × ℝ) → ℝ × ℝ),
    ValidPairActivation activation lift → Monotone lift →
    (ConvexOn ℝ Set.univ (fun z => (lift z).1) ∧
      ConvexOn ℝ Set.univ (fun z => (lift z).2)) →
    ∀ (positive negative : Matrix (Fin k) (Fin m) ℝ),
      (∀ i j, 0 ≤ positive i j) → (∀ i j, 0 ≤ negative i j) →
    ∀ (positiveBias negativeBias : Vec k),
      Monotone (fun input : Vec n =>
        backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : Vec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)).1 j)) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : Vec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)).2 j)) ∧
      ∀ input : Vec n,
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)).1 -
          (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)).2 =
          affineLayer positive negative positiveBias negativeBias
            (backbone.forwardWith activation input))
theorem _ThesisExactChecks.target_391 : _ThesisExpectedTypes.type_391 := by exact @HiddenMonotonicity.Network.affine_dc_decomposition
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_dc_decomposition
  let expected ← getConstInfo `_ThesisExactChecks.target_391
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_dc_decomposition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_dc_decomposition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexMonotoneReadout do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_dc_decomposition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_391) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_dc_decomposition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_dc_decomposition"
#check @HiddenMonotonicity.Network.affine_dc_decomposition
#print axioms _ThesisExactChecks.target_391

section
open HiddenMonotonicity
def _ThesisExpectedTypes.type_392 : Prop := (∀ (n m k : ℕ) (backbone : Network n m), backbone.Nonnegative →
    ∀ (activation : ℝ → ℝ) (lift : (ℝ × ℝ) → ℝ × ℝ),
    ValidPairActivation activation lift → Monotone lift →
    (ConvexOn ℝ Set.univ (fun z => (lift z).1) ∧
      ConvexOn ℝ Set.univ (fun z => (lift z).2)) →
    ∀ (positive negative : Matrix (Fin k) (Fin m) ℝ),
      (∀ i j, 0 ≤ positive i j) → (∀ i j, 0 ≤ negative i j) →
    ∀ (positiveBias negativeBias : Vec k),
      (∀ j, ConvexOn ℝ Set.univ (fun input : Vec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias
          ((fun i => max (input i) 0), (fun i => max (-input i) 0))).1 j)) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : Vec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias
          ((fun i => max (input i) 0), (fun i => max (-input i) 0))).2 j)) ∧
      ∀ input : Vec n,
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias
          ((fun i => max (input i) 0), (fun i => max (-input i) 0))).1 -
          (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias
            ((fun i => max (input i) 0), (fun i => max (-input i) 0))).2 =
          affineLayer positive negative positiveBias negativeBias
            (backbone.forwardWith activation input))
theorem _ThesisExactChecks.target_392 : _ThesisExpectedTypes.type_392 := by exact @HiddenMonotonicity.Network.affine_signed_input_dc_decomposition
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_signed_input_dc_decomposition
  let expected ← getConstInfo `_ThesisExactChecks.target_392
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_signed_input_dc_decomposition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_signed_input_dc_decomposition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexMonotoneReadout do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_signed_input_dc_decomposition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_392) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_signed_input_dc_decomposition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_signed_input_dc_decomposition"
#check @HiddenMonotonicity.Network.affine_signed_input_dc_decomposition
#print axioms _ThesisExactChecks.target_392

section
def _ThesisExpectedTypes.type_393 : Prop := (∀ θ : ℝ, 0 < θ → ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (HiddenMonotonicity.SmoothDC.explicitSoftplusPair θ z).1) ∧ ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (HiddenMonotonicity.SmoothDC.explicitSoftplusPair θ z).2) ∧ Monotone (fun z : ℝ × ℝ => (HiddenMonotonicity.SmoothDC.explicitSoftplusPair θ z).1) ∧ Monotone (fun z : ℝ × ℝ => (HiddenMonotonicity.SmoothDC.explicitSoftplusPair θ z).2) ∧ HiddenMonotonicity.ValidPairActivation (Thesis.Regularization.softplus θ) (HiddenMonotonicity.SmoothDC.explicitSoftplusPair θ) ∧ HiddenMonotonicity.NonnegativePairActivation (HiddenMonotonicity.SmoothDC.explicitSoftplusPair θ))
theorem _ThesisExactChecks.target_393 : _ThesisExpectedTypes.type_393 := by exact @HiddenMonotonicity.SmoothDC.softplus_explicit_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.softplus_explicit_split
  let expected ← getConstInfo `_ThesisExactChecks.target_393
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.softplus_explicit_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.softplus_explicit_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftplus do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.softplus_explicit_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_393) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.softplus_explicit_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.softplus_explicit_split"
#check @HiddenMonotonicity.SmoothDC.softplus_explicit_split
#print axioms _ThesisExactChecks.target_393

section
def _ThesisExpectedTypes.type_394 : Prop := (∀ θ : ℝ, 0 < θ → ∀ x y : ℝ, HiddenMonotonicity.SmoothDC.explicitSoftplusFirst θ (x,y) = θ * Real.log (Real.exp (x / θ) + Real.exp (y / θ)))
theorem _ThesisExactChecks.target_394 : _ThesisExpectedTypes.type_394 := by exact @HiddenMonotonicity.SmoothDC.explicitSoftplusFirst_logsumexp
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.explicitSoftplusFirst_logsumexp
  let expected ← getConstInfo `_ThesisExactChecks.target_394
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.explicitSoftplusFirst_logsumexp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.explicitSoftplusFirst_logsumexp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftplus do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.explicitSoftplusFirst_logsumexp"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_394) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.explicitSoftplusFirst_logsumexp: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.explicitSoftplusFirst_logsumexp"
#check @HiddenMonotonicity.SmoothDC.explicitSoftplusFirst_logsumexp
#print axioms _ThesisExactChecks.target_394

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_395 : Prop := (ConvexOn ℝ Set.univ (fun z => (sigmoidExplicitPair z).1) ∧ ConvexOn ℝ Set.univ (fun z => (sigmoidExplicitPair z).2) ∧ Monotone sigmoidExplicitPair ∧ ValidPairActivation Real.sigmoid sigmoidExplicitPair ∧ NonnegativePairActivation sigmoidExplicitPair)
theorem _ThesisExactChecks.target_395 : _ThesisExpectedTypes.type_395 := by exact @HiddenMonotonicity.SmoothDC.sigmoid_explicit_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.sigmoid_explicit_split
  let expected ← getConstInfo `_ThesisExactChecks.target_395
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.sigmoid_explicit_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.sigmoid_explicit_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSigmoidSoftplus do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.sigmoid_explicit_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_395) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.sigmoid_explicit_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.sigmoid_explicit_split"
#check @HiddenMonotonicity.SmoothDC.sigmoid_explicit_split
#print axioms _ThesisExactChecks.target_395

section
open HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_396 : Prop := (∀ x y : ℝ, sigmoidExplicitPair (x, y) = (if x ≤ y then Real.sigmoid (x - y) + y / 4 else 1 / 2 + x / 4, if x ≤ y then y / 4 else 1 / 2 + x / 4 - Real.sigmoid (x - y)))
theorem _ThesisExactChecks.target_396 : _ThesisExpectedTypes.type_396 := by exact @HiddenMonotonicity.SmoothDC.sigmoidExplicitPair_closed_form
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.sigmoidExplicitPair_closed_form
  let expected ← getConstInfo `_ThesisExactChecks.target_396
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.sigmoidExplicitPair_closed_form"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.sigmoidExplicitPair_closed_form | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSigmoidSoftplus do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.sigmoidExplicitPair_closed_form"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_396) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.sigmoidExplicitPair_closed_form: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.sigmoidExplicitPair_closed_form"
#check @HiddenMonotonicity.SmoothDC.sigmoidExplicitPair_closed_form
#print axioms _ThesisExactChecks.target_396

section
def _ThesisExpectedTypes.type_397 : Prop := (ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair z).1) ∧ ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair z).2) ∧ Monotone (fun z : ℝ × ℝ => (HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair z).1) ∧ Monotone (fun z : ℝ × ℝ => (HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair z).2) ∧ HiddenMonotonicity.ValidPairActivation Real.sigmoid HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair ∧ HiddenMonotonicity.NonnegativePairActivation HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair)
theorem _ThesisExactChecks.target_397 : _ThesisExpectedTypes.type_397 := by exact @HiddenMonotonicity.SmoothDC.sigmoid_smooth_explicit_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.sigmoid_smooth_explicit_split
  let expected ← getConstInfo `_ThesisExactChecks.target_397
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.sigmoid_smooth_explicit_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.sigmoid_smooth_explicit_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSigmoidSmooth do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.sigmoid_smooth_explicit_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_397) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.sigmoid_smooth_explicit_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.sigmoid_smooth_explicit_split"
#check @HiddenMonotonicity.SmoothDC.sigmoid_smooth_explicit_split
#print axioms _ThesisExactChecks.target_397

section
def _ThesisExpectedTypes.type_398 : Prop := (∀ x y : ℝ, HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair (x,y) = ((Real.log (Real.exp x + Real.exp y) + Real.sigmoid (x-y)) / 2, (Real.log (Real.exp x + Real.exp y) - Real.sigmoid (x-y)) / 2))
theorem _ThesisExactChecks.target_398 : _ThesisExpectedTypes.type_398 := by exact @HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_logsumexp
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_logsumexp
  let expected ← getConstInfo `_ThesisExactChecks.target_398
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_logsumexp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_logsumexp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSigmoidSmooth do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_logsumexp"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_398) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_logsumexp: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_logsumexp"
#check @HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_logsumexp
#print axioms _ThesisExactChecks.target_398

section
def _ThesisExpectedTypes.type_399 : Prop := (ContDiff ℝ ⊤ HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair)
theorem _ThesisExactChecks.target_399 : _ThesisExpectedTypes.type_399 := by exact @HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_contDiff
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_contDiff
  let expected ← getConstInfo `_ThesisExactChecks.target_399
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_contDiff"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_contDiff | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSigmoidSmooth do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_contDiff"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_399) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_contDiff: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_contDiff"
#check @HiddenMonotonicity.SmoothDC.explicitSigmoidSmoothPair_contDiff
#print axioms _ThesisExactChecks.target_399

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_400 : Prop := (∀ β : ℝ, 0 < β → ConvexOn ℝ Set.univ (explicitSwishFirst β) ∧ ConvexOn ℝ Set.univ (explicitSwishSecond β) ∧ Monotone (explicitSwishFirst β) ∧ Monotone (explicitSwishSecond β) ∧ ∀ z : ℝ × ℝ, explicitSwishFirst β z - explicitSwishSecond β z = (z.1 - z.2) * Real.sigmoid (β * (z.1 - z.2)))
theorem _ThesisExactChecks.target_400 : _ThesisExpectedTypes.type_400 := by exact @HiddenMonotonicity.SmoothDC.explicitSwish_lift
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.explicitSwish_lift
  let expected ← getConstInfo `_ThesisExactChecks.target_400
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.explicitSwish_lift"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.explicitSwish_lift | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSwish do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.explicitSwish_lift"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_400) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.explicitSwish_lift: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.explicitSwish_lift"
#check @HiddenMonotonicity.SmoothDC.explicitSwish_lift
#print axioms _ThesisExactChecks.target_400

section
open HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_401 : Prop := (∀ β : ℝ, ∀ z : ℝ × ℝ, explicitSwishFirst β z = 2 / β * Real.log (1 + Real.exp (β * (z.1 - z.2))) + 2 * z.2 ∧ explicitSwishSecond β z = 2 / β * Real.log (1 + Real.exp (β * (z.1 - z.2))) - (z.1 - z.2) * Real.sigmoid (β * (z.1 - z.2)) + 2 * z.2)
theorem _ThesisExactChecks.target_401 : _ThesisExpectedTypes.type_401 := by exact @HiddenMonotonicity.SmoothDC.explicitSwish_closed
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.explicitSwish_closed
  let expected ← getConstInfo `_ThesisExactChecks.target_401
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.explicitSwish_closed"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.explicitSwish_closed | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSwish do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.explicitSwish_closed"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_401) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.explicitSwish_closed: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.explicitSwish_closed"
#check @HiddenMonotonicity.SmoothDC.explicitSwish_closed
#print axioms _ThesisExactChecks.target_401

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_402 : Prop := (∀ β : ℝ, 0 < β → NonnegativePairActivation (explicitSwishPair β))
theorem _ThesisExactChecks.target_402 : _ThesisExpectedTypes.type_402 := by exact @HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_402
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSwish do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_402) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative"
#check @HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative
#print axioms _ThesisExactChecks.target_402

section
open HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_403 : Prop := (∀ β : ℝ, 0 < β → ∀ x : ℝ, (0 < curvature (swish β) x ↔ |β * x| < swishTurningPoint) ∧ (curvature (swish β) x < 0 ↔ swishTurningPoint < |β * x|) ∧ (curvature (swish β) x = 0 ↔ |β * x| = swishTurningPoint))
theorem _ThesisExactChecks.target_403 : _ThesisExpectedTypes.type_403 := by exact @HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign
  let expected ← getConstInfo `_ThesisExactChecks.target_403
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SwishThreshold do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_403) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign"
#check @HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign
#print axioms _ThesisExactChecks.target_403

section
open HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_404 : Prop := (∀ (f d : ℝ → ℝ) (a b : ℝ), a < b → (∀ x, HasDerivAt f (d x) x) → AntitoneOn d (Set.Iic a) → MonotoneOn d (Set.Icc a b) → AntitoneOn d (Set.Ici b) → (∀ x, x ≤ a → d x ≤ 0) → (∀ x, b ≤ x → 0 ≤ d x) → ConvexOn ℝ Set.univ (asymmetricLift (centralConvexP f d a b) (d b - d a)) ∧ ConvexOn ℝ Set.univ (asymmetricLift (centralConvexQ f d a b) (d b - d a)) ∧ Monotone (asymmetricLift (centralConvexP f d a b) (d b - d a)) ∧ Monotone (asymmetricLift (centralConvexQ f d a b) (d b - d a)) ∧ ∀ z : ℝ × ℝ, asymmetricLift (centralConvexP f d a b) (d b - d a) z - asymmetricLift (centralConvexQ f d a b) (d b - d a) z = f (z.1 - z.2))
theorem _ThesisExactChecks.target_404 : _ThesisExpectedTypes.type_404 := by exact @HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split
  let expected ← getConstInfo `_ThesisExactChecks.target_404
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TwoInflectionDC do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_404) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split"
#check @HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split
#print axioms _ThesisExactChecks.target_404

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_405 : Prop := (ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).1) ∧ ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).2) ∧ Monotone (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).1) ∧ Monotone (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).2) ∧ ValidPairActivation gaussianGelu explicitGaussianGeluPair ∧ NonnegativePairActivation explicitGaussianGeluPair)
theorem _ThesisExactChecks.target_405 : _ThesisExpectedTypes.type_405 := by exact @HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split
  let expected ← getConstInfo `_ThesisExactChecks.target_405
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitGELU do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_405) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split"
#check @HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split
#print axioms _ThesisExactChecks.target_405

section
open HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_406 : Prop := (∀ x y : ℝ, explicitGaussianGeluPair (x, y) = (2 * (gaussianGelu (x - y) + standardGaussianDensity (x - y)) + 2 * y, gaussianGelu (x - y) + 2 * standardGaussianDensity (x - y) + 2 * y))
theorem _ThesisExactChecks.target_406 : _ThesisExpectedTypes.type_406 := by exact @HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula
  let expected ← getConstInfo `_ThesisExactChecks.target_406
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitGELU do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_406) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula"
#check @HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula
#print axioms _ThesisExactChecks.target_406

section
open HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_407 : Prop := (∀ {x : ℝ}, -Real.sqrt 2 ≤ x ∧ x ≤ Real.sqrt 2 → gaussianGeluFirst (-Real.sqrt 2) ≤ gaussianGeluFirst x ∧ gaussianGeluFirst x ≤ gaussianGeluFirst (Real.sqrt 2))
theorem _ThesisExactChecks.target_407 : _ThesisExpectedTypes.type_407 := by exact @HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds
  let expected ← getConstInfo `_ThesisExactChecks.target_407
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.GELUInflectionBounds do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_407) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds"
#check @HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds
#print axioms _ThesisExactChecks.target_407

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_408 : Prop := (∀ a : ModernActivation, ConvexPairActivation (curvatureLiftPair a.eval) ∧ Monotone (curvatureLiftPair a.eval) ∧ ValidPairActivation a.eval (curvatureLiftPair a.eval) ∧ NonnegativePairActivation (curvatureLiftPair a.eval))
theorem _ThesisExactChecks.target_408 : _ThesisExpectedTypes.type_408 := by exact @HiddenMonotonicity.SmoothDC.modern_curvature_pair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.modern_curvature_pair
  let expected ← getConstInfo `_ThesisExactChecks.target_408
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.modern_curvature_pair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.modern_curvature_pair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernMonotoneDC do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.modern_curvature_pair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_408) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.modern_curvature_pair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.modern_curvature_pair"
#check @HiddenMonotonicity.SmoothDC.modern_curvature_pair
#print axioms _ThesisExactChecks.target_408

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_409 : Prop := (∀ {n m : ℕ} (net : Network n m), net.Nonnegative → ∀ a : ModernActivation, Monotone (net.decomposeWith (curvatureLiftPair a.eval)) ∧ (∀ i, ConvexOn ℝ Set.univ (fun x : PairVec n => (net.decomposeWith (curvatureLiftPair a.eval) x).1 i)) ∧ (∀ i, ConvexOn ℝ Set.univ (fun x : PairVec n => (net.decomposeWith (curvatureLiftPair a.eval) x).2 i)) ∧ ∀ x : PairVec n, (net.decomposeWith (curvatureLiftPair a.eval) x).1 - (net.decomposeWith (curvatureLiftPair a.eval) x).2 = net.forwardWith a.eval (x.1 - x.2))
theorem _ThesisExactChecks.target_409 : _ThesisExpectedTypes.type_409 := by exact @HiddenMonotonicity.SmoothDC.modern_curvature_network
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.modern_curvature_network
  let expected ← getConstInfo `_ThesisExactChecks.target_409
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.modern_curvature_network"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.modern_curvature_network | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernMonotoneDC do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.modern_curvature_network"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_409) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.modern_curvature_network: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.modern_curvature_network"
#check @HiddenMonotonicity.SmoothDC.modern_curvature_network
#print axioms _ThesisExactChecks.target_409

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_410 : Prop := (∀ {n m : ℕ} (net : Network n m), net.NonnegativeParameters → ∀ (a : ModernActivation) (x : PairVec n), (0 ≤ x.1 ∧ 0 ≤ x.2) → 0 ≤ (net.decomposeWith (curvatureLiftPair a.eval) x).1 ∧ 0 ≤ (net.decomposeWith (curvatureLiftPair a.eval) x).2)
theorem _ThesisExactChecks.target_410 : _ThesisExpectedTypes.type_410 := by exact @HiddenMonotonicity.SmoothDC.modern_curvature_network_nonnegative
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.modern_curvature_network_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_410
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.modern_curvature_network_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.modern_curvature_network_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernMonotoneDC do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.modern_curvature_network_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_410) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.modern_curvature_network_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.modern_curvature_network_nonnegative"
#check @HiddenMonotonicity.SmoothDC.modern_curvature_network_nonnegative
#print axioms _ThesisExactChecks.target_410

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_411 : Prop := (∀ {n m k : ℕ} (net : Network n m), net.Nonnegative → ∀ (a : ModernActivation) (wp wn : Matrix (Fin k) (Fin m) ℝ), (∀ i j, 0 ≤ wp i j) → (∀ i j, 0 ≤ wn i j) → ∀ bp bn : Vec k, Monotone (net.affineDecomposeWith (curvatureLiftPair a.eval) wp wn bp bn) ∧ (∀ i, ConvexOn ℝ Set.univ (fun x : PairVec n => (net.affineDecomposeWith (curvatureLiftPair a.eval) wp wn bp bn x).1 i)) ∧ (∀ i, ConvexOn ℝ Set.univ (fun x : PairVec n => (net.affineDecomposeWith (curvatureLiftPair a.eval) wp wn bp bn x).2 i)) ∧ ∀ x : PairVec n, (net.affineDecomposeWith (curvatureLiftPair a.eval) wp wn bp bn x).1 - (net.affineDecomposeWith (curvatureLiftPair a.eval) wp wn bp bn x).2 = affineLayer wp wn bp bn (net.forwardWith a.eval (x.1 - x.2)))
theorem _ThesisExactChecks.target_411 : _ThesisExpectedTypes.type_411 := by exact @HiddenMonotonicity.SmoothDC.modern_curvature_affine_network
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.modern_curvature_affine_network
  let expected ← getConstInfo `_ThesisExactChecks.target_411
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.modern_curvature_affine_network"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.modern_curvature_affine_network | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ModernMonotoneDC do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.modern_curvature_affine_network"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_411) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.modern_curvature_affine_network: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.modern_curvature_affine_network"
#check @HiddenMonotonicity.SmoothDC.modern_curvature_affine_network
#print axioms _ThesisExactChecks.target_411

section
open HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_412 : Prop := (∀ x y : ℝ, ClosedFormActivation.relu.pair (x,y) = (max x y,y))
theorem _ThesisExactChecks.target_412 : _ThesisExpectedTypes.type_412 := by exact @HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair
  let expected ← getConstInfo `_ThesisExactChecks.target_412
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ClosedFormMonotoneDC do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_412) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair"
#check @HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair
#print axioms _ThesisExactChecks.target_412

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_413 : Prop := (∀ a : ClosedFormActivation, ConvexPairActivation a.pair ∧ Monotone a.pair ∧ ValidPairActivation a.eval a.pair ∧ NonnegativePairActivation a.pair)
theorem _ThesisExactChecks.target_413 : _ThesisExpectedTypes.type_413 := by exact @HiddenMonotonicity.SmoothDC.closed_form_activation_properties
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.closed_form_activation_properties
  let expected ← getConstInfo `_ThesisExactChecks.target_413
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.closed_form_activation_properties"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.closed_form_activation_properties | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ClosedFormMonotoneDC do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.closed_form_activation_properties"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_413) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.closed_form_activation_properties: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.closed_form_activation_properties"
#check @HiddenMonotonicity.SmoothDC.closed_form_activation_properties
#print axioms _ThesisExactChecks.target_413

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_414 : Prop := (∀ {n m k : ℕ} (net : Network n m), net.Nonnegative → ∀ (a : ClosedFormActivation) (wp wn : Matrix (Fin k) (Fin m) ℝ), (∀ i j, 0 ≤ wp i j) → (∀ i j, 0 ≤ wn i j) → ∀ bp bn : Vec k, Monotone (net.affineDecomposeWith a.pair wp wn bp bn) ∧ (∀ i, ConvexOn ℝ Set.univ (fun x : PairVec n => (net.affineDecomposeWith a.pair wp wn bp bn x).1 i)) ∧ (∀ i, ConvexOn ℝ Set.univ (fun x : PairVec n => (net.affineDecomposeWith a.pair wp wn bp bn x).2 i)) ∧ ∀ x : PairVec n, (net.affineDecomposeWith a.pair wp wn bp bn x).1 - (net.affineDecomposeWith a.pair wp wn bp bn x).2 = affineLayer wp wn bp bn (net.forwardWith a.eval (x.1 - x.2)))
theorem _ThesisExactChecks.target_414 : _ThesisExpectedTypes.type_414 := by exact @HiddenMonotonicity.SmoothDC.closed_form_affine_network
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.closed_form_affine_network
  let expected ← getConstInfo `_ThesisExactChecks.target_414
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.closed_form_affine_network"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.closed_form_affine_network | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ClosedFormMonotoneDC do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.closed_form_affine_network"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_414) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.closed_form_affine_network: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.closed_form_affine_network"
#check @HiddenMonotonicity.SmoothDC.closed_form_affine_network
#print axioms _ThesisExactChecks.target_414

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_415 : Prop := (∀ {n m k : ℕ} (net : Network n m), net.Nonnegative → ∀ (a : ClosedFormActivation) (wp wn : Matrix (Fin k) (Fin m) ℝ), (∀ i j, 0 ≤ wp i j) → (∀ i j, 0 ≤ wn i j) → ∀ bp bn : Vec k, Monotone (fun x : Vec n => net.affineDecomposeWith a.pair wp wn bp bn (x,0)) ∧ (∀ i, ConvexOn ℝ Set.univ (fun x : Vec n => (net.affineDecomposeWith a.pair wp wn bp bn (x,0)).1 i)) ∧ (∀ i, ConvexOn ℝ Set.univ (fun x : Vec n => (net.affineDecomposeWith a.pair wp wn bp bn (x,0)).2 i)) ∧ ∀ x : Vec n, (net.affineDecomposeWith a.pair wp wn bp bn (x,0)).1 - (net.affineDecomposeWith a.pair wp wn bp bn (x,0)).2 = affineLayer wp wn bp bn (net.forwardWith a.eval x))
theorem _ThesisExactChecks.target_415 : _ThesisExpectedTypes.type_415 := by exact @HiddenMonotonicity.SmoothDC.closed_form_affine_dc
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.closed_form_affine_dc
  let expected ← getConstInfo `_ThesisExactChecks.target_415
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.closed_form_affine_dc"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.closed_form_affine_dc | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ClosedFormMonotoneDC do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.closed_form_affine_dc"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_415) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.closed_form_affine_dc: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.closed_form_affine_dc"
#check @HiddenMonotonicity.SmoothDC.closed_form_affine_dc
#print axioms _ThesisExactChecks.target_415

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_416 : Prop := (∀ {ι : Type u} (f : (ι → ℝ) → ℝ), (∀ a v : ι → ℝ, ConvexOn ℝ Set.univ (fun t : ℝ => f (fun j => a j + t * v j))) → ConvexOn ℝ Set.univ f)
theorem _ThesisExactChecks.target_416 : _ThesisExpectedTypes.type_416.{u} := by exact @HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines
  let expected ← getConstInfo `_ThesisExactChecks.target_416
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MultivariateMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_416) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines"
#check @HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines
#print axioms _ThesisExactChecks.target_416

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_417 : Prop := (∀ {ι : Type u} (f : (ι → ℝ) → ℝ) (D : (ι → ℝ) → (ι → ℝ) → ℝ), (∀ (a v : ι → ℝ) (t : ℝ), HasDerivAt (fun s : ℝ => f (fun j => a j + s * v j)) (D (fun j => a j + t * v j) v) t) → (∀ z v : ι → ℝ, (∀ j, 0 ≤ v j) → 0 ≤ D z v) → Monotone f)
theorem _ThesisExactChecks.target_417 : _ThesisExpectedTypes.type_417.{u} := by exact @HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv
  let expected ← getConstInfo `_ThesisExactChecks.target_417
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MultivariateMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_417) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv"
#check @HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv
#print axioms _ThesisExactChecks.target_417

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_418 : Prop := (∀ {ι : Type u} [Fintype ι] (P : (ι → ℝ) → ℝ) (L c : ℝ), ConvexOn ℝ Set.univ P → ConvexOn ℝ Set.univ (HiddenMonotonicity.SoftmaxDC.multivariateLift P L c))
theorem _ThesisExactChecks.target_418 : _ThesisExpectedTypes.type_418.{u} := by exact @HiddenMonotonicity.SoftmaxDC.multivariateLift_convex.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.multivariateLift_convex
  let expected ← getConstInfo `_ThesisExactChecks.target_418
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_convex"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.multivariateLift_convex | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MultivariateMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_convex"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_418) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.multivariateLift_convex: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_convex"
#check @HiddenMonotonicity.SoftmaxDC.multivariateLift_convex
#print axioms _ThesisExactChecks.target_418

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_419 : Prop := (∀ {ι : Type u} [Fintype ι] (P : (ι → ℝ) → ℝ) (L c : ℝ), Monotone P → Monotone (fun x : ι → ℝ => L * (∑ j, x j) - P x) → Monotone (HiddenMonotonicity.SoftmaxDC.multivariateLift P L c))
theorem _ThesisExactChecks.target_419 : _ThesisExpectedTypes.type_419.{u} := by exact @HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone
  let expected ← getConstInfo `_ThesisExactChecks.target_419
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MultivariateMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_419) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone"
#check @HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone
#print axioms _ThesisExactChecks.target_419

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_420 : Prop := (∀ {ι : Type u} [Fintype ι] (P Q f : (ι → ℝ) → ℝ) (L c : ℝ), (∀ x, P x - Q x = f x) → ∀ z : (ι → ℝ) × (ι → ℝ), HiddenMonotonicity.SoftmaxDC.multivariateLift P L c z - HiddenMonotonicity.SoftmaxDC.multivariateLift Q L c z = f (z.1 - z.2))
theorem _ThesisExactChecks.target_420 : _ThesisExpectedTypes.type_420.{u} := by exact @HiddenMonotonicity.SoftmaxDC.multivariateLift_difference.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.multivariateLift_difference
  let expected ← getConstInfo `_ThesisExactChecks.target_420
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_difference"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.multivariateLift_difference | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MultivariateMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_difference"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_420) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.multivariateLift_difference: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_difference"
#check @HiddenMonotonicity.SoftmaxDC.multivariateLift_difference
#print axioms _ThesisExactChecks.target_420

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_421 : Prop := (∀ {ι : Type u} [Fintype ι] (P : (ι → ℝ) → ℝ) (L c : ℝ), Monotone (HiddenMonotonicity.SoftmaxDC.multivariateLift P L c) → c ≤ P 0 → ∀ z : (ι → ℝ) × (ι → ℝ), 0 ≤ z → 0 ≤ HiddenMonotonicity.SoftmaxDC.multivariateLift P L c z)
theorem _ThesisExactChecks.target_421 : _ThesisExpectedTypes.type_421.{u} := by exact @HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_421
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MultivariateMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_421) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative"
#check @HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative
#print axioms _ThesisExactChecks.target_421

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_422 : Prop := (∀ {ι : Type u} [Fintype ι] (p : ι → ℝ), (∀ j, 0 ≤ p j) → (∑ j, p j) = 1 → ∀ (w : ι → ℝ), (∀ j, 0 ≤ w j) → ∀ i, -(∑ j, p j * w j) ≤ p i * (w i - ∑ j, p j * w j) ∧ p i * (w i - ∑ j, p j * w j) ≤ ∑ j, p j * w j)
theorem _ThesisExactChecks.target_422 : _ThesisExpectedTypes.type_422.{u} := by exact @HiddenMonotonicity.SoftmaxDC.probability_second_bounds.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.probability_second_bounds
  let expected ← getConstInfo `_ThesisExactChecks.target_422
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.probability_second_bounds"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.probability_second_bounds | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxProbability do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.probability_second_bounds"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_422) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.probability_second_bounds: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.probability_second_bounds"
#check @HiddenMonotonicity.SoftmaxDC.probability_second_bounds
#print axioms _ThesisExactChecks.target_422

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_423 : Prop := (∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (p : ι → ℝ), (∀ j, 0 ≤ p j) → (∑ j, p j) = 1 → ∀ i j, 0 ≤ (p j + p i * ((if i = j then 1 else 0) - p j)) / 2 ∧ (p j + p i * ((if i = j then 1 else 0) - p j)) / 2 ≤ (1 : ℝ) / 2)
theorem _ThesisExactChecks.target_423 : _ThesisExpectedTypes.type_423.{u} := by exact @HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds
  let expected ← getConstInfo `_ThesisExactChecks.target_423
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxProbability do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_423) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds"
#check @HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds
#print axioms _ThesisExactChecks.target_423

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_424 : Prop := (∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (p : ι → ℝ), (∀ j, 0 ≤ p j) → (∑ j, p j) = 1 → ∀ i j, 0 ≤ (p j - p i * ((if i = j then 1 else 0) - p j)) / 2 ∧ (p j - p i * ((if i = j then 1 else 0) - p j)) / 2 ≤ (1 : ℝ) / 2)
theorem _ThesisExactChecks.target_424 : _ThesisExpectedTypes.type_424.{u} := by exact @HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds
  let expected ← getConstInfo `_ThesisExactChecks.target_424
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxProbability do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_424) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds"
#check @HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds
#print axioms _ThesisExactChecks.target_424

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_425 : Prop := (∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (p v : ι → ℝ) (i : ι), (∑ j, ((p j + p i * ((if i = j then 1 else 0) - p j)) / 2) * v j) = ((∑ j, p j * v j) + p i * (v i - ∑ j, p j * v j)) / 2)
theorem _ThesisExactChecks.target_425 : _ThesisExpectedTypes.type_425.{u} := by exact @HiddenMonotonicity.SoftmaxDC.plusCoeff_sum.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.plusCoeff_sum
  let expected ← getConstInfo `_ThesisExactChecks.target_425
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.plusCoeff_sum"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.plusCoeff_sum | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxProbability do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.plusCoeff_sum"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_425) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.plusCoeff_sum: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.plusCoeff_sum"
#check @HiddenMonotonicity.SoftmaxDC.plusCoeff_sum
#print axioms _ThesisExactChecks.target_425

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_426 : Prop := (∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (p v : ι → ℝ) (i : ι), (∑ j, ((p j - p i * ((if i = j then 1 else 0) - p j)) / 2) * v j) = ((∑ j, p j * v j) - p i * (v i - ∑ j, p j * v j)) / 2)
theorem _ThesisExactChecks.target_426 : _ThesisExpectedTypes.type_426.{u} := by exact @HiddenMonotonicity.SoftmaxDC.minusCoeff_sum.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.minusCoeff_sum
  let expected ← getConstInfo `_ThesisExactChecks.target_426
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.minusCoeff_sum"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.minusCoeff_sum | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxProbability do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.minusCoeff_sum"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_426) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.minusCoeff_sum: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.minusCoeff_sum"
#check @HiddenMonotonicity.SoftmaxDC.minusCoeff_sum
#print axioms _ThesisExactChecks.target_426

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_427 : Prop := (∀ {ι : Type u} [Fintype ι] (c v : ι → ℝ), (∀ j, 0 ≤ c j ∧ c j ≤ (1 : ℝ) / 2) → (∀ j, 0 ≤ v j) → 0 ≤ ∑ j, c j * v j ∧ (∑ j, c j * v j) ≤ (∑ j, v j) / 2)
theorem _ThesisExactChecks.target_427 : _ThesisExpectedTypes.type_427.{u} := by exact @HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds
  let expected ← getConstInfo `_ThesisExactChecks.target_427
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxProbability do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_427) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds"
#check @HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds
#print axioms _ThesisExactChecks.target_427

section
universe u
open HiddenMonotonicity.SoftmaxDC
def _ThesisExpectedTypes.type_428 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (a v : ι → ℝ) (t : ℝ), HasDerivAt (fun r => logSumExp (affineLine a v r)) (mean (affineLine a v t) v) t)
theorem _ThesisExactChecks.target_428 : _ThesisExpectedTypes.type_428.{u} := by exact @HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative
  let expected ← getConstInfo `_ThesisExactChecks.target_428
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxLineCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_428) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative"
#check @HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative
#print axioms _ThesisExactChecks.target_428

section
universe u
open HiddenMonotonicity.SoftmaxDC
def _ThesisExpectedTypes.type_429 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (a v : ι → ℝ) (t : ℝ), HasDerivAt (fun r => mean (affineLine a v r) v) (variance (affineLine a v t) v) t)
theorem _ThesisExactChecks.target_429 : _ThesisExpectedTypes.type_429.{u} := by exact @HiddenMonotonicity.SoftmaxDC.mean_line_derivative.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.mean_line_derivative
  let expected ← getConstInfo `_ThesisExactChecks.target_429
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.mean_line_derivative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.mean_line_derivative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxLineCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.mean_line_derivative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_429) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.mean_line_derivative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.mean_line_derivative"
#check @HiddenMonotonicity.SoftmaxDC.mean_line_derivative
#print axioms _ThesisExactChecks.target_429

section
universe u
open HiddenMonotonicity.SoftmaxDC
def _ThesisExpectedTypes.type_430 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (a v : ι → ℝ) (t : ℝ) (i : ι), HasDerivAt (fun r => softmax (affineLine a v r) i) (softmax (affineLine a v t) i * (v i - mean (affineLine a v t) v)) t)
theorem _ThesisExactChecks.target_430 : _ThesisExpectedTypes.type_430.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmax_line_derivative.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmax_line_derivative
  let expected ← getConstInfo `_ThesisExactChecks.target_430
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmax_line_derivative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmax_line_derivative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxLineCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmax_line_derivative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_430) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmax_line_derivative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmax_line_derivative"
#check @HiddenMonotonicity.SoftmaxDC.softmax_line_derivative
#print axioms _ThesisExactChecks.target_430

section
universe u
open HiddenMonotonicity.SoftmaxDC
def _ThesisExpectedTypes.type_431 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (a v : ι → ℝ) (t : ℝ) (i : ι), HasDerivAt (fun r => softmax (affineLine a v r) i * (v i - mean (affineLine a v r) v)) (softmax (affineLine a v t) i * ((v i - mean (affineLine a v t) v) ^ 2 - variance (affineLine a v t) v)) t)
theorem _ThesisExactChecks.target_431 : _ThesisExpectedTypes.type_431.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative
  let expected ← getConstInfo `_ThesisExactChecks.target_431
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxLineCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_431) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative"
#check @HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative
#print axioms _ThesisExactChecks.target_431

section
universe u
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
def _ThesisExpectedTypes.type_432 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (z : ι → ℝ), (∑ j, softmax z j) = 1)
theorem _ThesisExactChecks.target_432 : _ThesisExpectedTypes.type_432.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmax_sum_one.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmax_sum_one
  let expected ← getConstInfo `_ThesisExactChecks.target_432
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmax_sum_one"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmax_sum_one | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxLineCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmax_sum_one"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_432) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmax_sum_one: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmax_sum_one"
#check @HiddenMonotonicity.SoftmaxDC.softmax_sum_one
#print axioms _ThesisExactChecks.target_432

section
universe u
open HiddenMonotonicity.SoftmaxDC
def _ThesisExpectedTypes.type_433 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (z : ι → ℝ), 0 < expSum z)
theorem _ThesisExactChecks.target_433 : _ThesisExpectedTypes.type_433.{u} := by exact @HiddenMonotonicity.SoftmaxDC.expSum_pos.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.expSum_pos
  let expected ← getConstInfo `_ThesisExactChecks.target_433
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.expSum_pos"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.expSum_pos | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxLineCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.expSum_pos"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_433) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.expSum_pos: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.expSum_pos"
#check @HiddenMonotonicity.SoftmaxDC.expSum_pos
#print axioms _ThesisExactChecks.target_433

section
universe u
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
def _ThesisExpectedTypes.type_434 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (i : ι),
ConvexOn ℝ Set.univ (softmaxSplitFirst i) ∧
ConvexOn ℝ Set.univ (softmaxSplitSecond i) ∧
Monotone (softmaxSplitFirst i) ∧ Monotone (softmaxSplitSecond i) ∧
(∀ z : (ι → ℝ) × (ι → ℝ), softmaxSplitFirst i z - softmaxSplitSecond i z = softmax (z.1-z.2) i) ∧
(∀ z : (ι → ℝ) × (ι → ℝ), 0 ≤ z → 0 ≤ softmaxSplitFirst i z ∧ 0 ≤ softmaxSplitSecond i z))
theorem _ThesisExactChecks.target_434 : _ThesisExpectedTypes.type_434.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmax_split_properties.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmax_split_properties
  let expected ← getConstInfo `_ThesisExactChecks.target_434
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmax_split_properties"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmax_split_properties | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftmax do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmax_split_properties"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_434) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmax_split_properties: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmax_split_properties"
#check @HiddenMonotonicity.SoftmaxDC.softmax_split_properties
#print axioms _ThesisExactChecks.target_434

section
universe u
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
def _ThesisExpectedTypes.type_435 : Prop := (∀ {ι : Type u} [Fintype ι] (i : ι) (x y : ι → ℝ),
softmaxSplitFirst i (x,y) =
(Real.log (∑ j, Real.exp (x j-y j)) + Real.exp (x i-y i)/(∑ j, Real.exp (x j-y j)) + ∑ j, y j)/2 -
(Real.log (Fintype.card ι)-1/Fintype.card ι)/2)
theorem _ThesisExactChecks.target_435 : _ThesisExpectedTypes.type_435.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula
  let expected ← getConstInfo `_ThesisExactChecks.target_435
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftmax do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_435) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula"
#check @HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula
#print axioms _ThesisExactChecks.target_435

section
universe u
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
def _ThesisExpectedTypes.type_436 : Prop := (∀ {ι : Type u} [Fintype ι] (i : ι) (x y : ι → ℝ),
softmaxSplitSecond i (x,y) =
(Real.log (∑ j, Real.exp (x j-y j)) - Real.exp (x i-y i)/(∑ j, Real.exp (x j-y j)) + ∑ j, y j)/2 -
(Real.log (Fintype.card ι)-1/Fintype.card ι)/2)
theorem _ThesisExactChecks.target_436 : _ThesisExpectedTypes.type_436.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula
  let expected ← getConstInfo `_ThesisExactChecks.target_436
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftmax do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_436) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula"
#check @HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula
#print axioms _ThesisExactChecks.target_436

section
universe u
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
def _ThesisExpectedTypes.type_437 : Prop := (∀ {ι : Type u} [Fintype ι] (i : ι) (z : (ι → ℝ) × (ι → ℝ)),
softmaxSplitFirst i z-softmaxSplitSecond i z=softmax (z.1-z.2) i)
theorem _ThesisExactChecks.target_437 : _ThesisExpectedTypes.type_437.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference
  let expected ← getConstInfo `_ThesisExactChecks.target_437
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftmax do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_437) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference"
#check @HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference
#print axioms _ThesisExactChecks.target_437

section
universe u
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
def _ThesisExpectedTypes.type_438 : Prop := (∀ {ι : Type u} [Fintype ι] (i : ι), softmaxSplitFirst i 0=1/Fintype.card ι)
theorem _ThesisExactChecks.target_438 : _ThesisExpectedTypes.type_438.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero
  let expected ← getConstInfo `_ThesisExactChecks.target_438
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftmax do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_438) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero"
#check @HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero
#print axioms _ThesisExactChecks.target_438

section
universe u
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
def _ThesisExpectedTypes.type_439 : Prop := (∀ {ι : Type u} [Fintype ι] (i : ι), softmaxSplitSecond i 0=0)
theorem _ThesisExactChecks.target_439 : _ThesisExpectedTypes.type_439.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero
  let expected ← getConstInfo `_ThesisExactChecks.target_439
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftmax do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_439) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero"
#check @HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero
#print axioms _ThesisExactChecks.target_439

section
def _ThesisExpectedTypes.type_440 : Prop := (∀ z : HiddenMonotonicity.TransformerDC.FourStreams, (HiddenMonotonicity.TransformerDC.productSplit z).1 - (HiddenMonotonicity.TransformerDC.productSplit z).2 = (z.1.1 - z.1.2) * (z.2.1 - z.2.2))
theorem _ThesisExactChecks.target_440 : _ThesisExpectedTypes.type_440 := by exact @HiddenMonotonicity.TransformerDC.productSplit_exact
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.productSplit_exact
  let expected ← getConstInfo `_ThesisExactChecks.target_440
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.productSplit_exact"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.productSplit_exact | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PolarizedProductDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.productSplit_exact"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_440) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.productSplit_exact: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.productSplit_exact"
#check @HiddenMonotonicity.TransformerDC.productSplit_exact
#print axioms _ThesisExactChecks.target_440

section
def _ThesisExpectedTypes.type_441 : Prop := (∀ z : HiddenMonotonicity.TransformerDC.FourStreams, 0 ≤ HiddenMonotonicity.TransformerDC.productSplit z)
theorem _ThesisExactChecks.target_441 : _ThesisExpectedTypes.type_441 := by exact @HiddenMonotonicity.TransformerDC.productSplit_nonnegative
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.productSplit_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_441
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.productSplit_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.productSplit_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PolarizedProductDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.productSplit_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_441) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.productSplit_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.productSplit_nonnegative"
#check @HiddenMonotonicity.TransformerDC.productSplit_nonnegative
#print axioms _ThesisExactChecks.target_441

section
def _ThesisExpectedTypes.type_442 : Prop := (ConvexOn ℝ Set.univ (fun z : HiddenMonotonicity.TransformerDC.FourStreams => (HiddenMonotonicity.TransformerDC.productSplit z).1) ∧ ConvexOn ℝ Set.univ (fun z : HiddenMonotonicity.TransformerDC.FourStreams => (HiddenMonotonicity.TransformerDC.productSplit z).2))
theorem _ThesisExactChecks.target_442 : _ThesisExpectedTypes.type_442 := by exact @HiddenMonotonicity.TransformerDC.productSplit_convex
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.productSplit_convex
  let expected ← getConstInfo `_ThesisExactChecks.target_442
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.productSplit_convex"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.productSplit_convex | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PolarizedProductDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.productSplit_convex"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_442) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.productSplit_convex: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.productSplit_convex"
#check @HiddenMonotonicity.TransformerDC.productSplit_convex
#print axioms _ThesisExactChecks.target_442

section
def _ThesisExpectedTypes.type_443 : Prop := (MonotoneOn HiddenMonotonicity.TransformerDC.productSplit (Set.Ici (0 : HiddenMonotonicity.TransformerDC.FourStreams)))
theorem _ThesisExactChecks.target_443 : _ThesisExpectedTypes.type_443 := by exact @HiddenMonotonicity.TransformerDC.productSplit_monotoneOn
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.productSplit_monotoneOn
  let expected ← getConstInfo `_ThesisExactChecks.target_443
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.productSplit_monotoneOn"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.productSplit_monotoneOn | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PolarizedProductDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.productSplit_monotoneOn"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_443) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.productSplit_monotoneOn: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.productSplit_monotoneOn"
#check @HiddenMonotonicity.TransformerDC.productSplit_monotoneOn
#print axioms _ThesisExactChecks.target_443

section
universe u
def _ThesisExpectedTypes.type_444 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (s : Set E) (A B C D : E → ℝ), ConvexOn ℝ s A → ConvexOn ℝ s B → ConvexOn ℝ s C → ConvexOn ℝ s D → (∀ x ∈ s, 0 ≤ A x) → (∀ x ∈ s, 0 ≤ B x) → (∀ x ∈ s, 0 ≤ C x) → (∀ x ∈ s, 0 ≤ D x) → ConvexOn ℝ s (fun x => (HiddenMonotonicity.TransformerDC.productSplit ((A x, B x), (C x, D x))).1) ∧ ConvexOn ℝ s (fun x => (HiddenMonotonicity.TransformerDC.productSplit ((A x, B x), (C x, D x))).2))
theorem _ThesisExactChecks.target_444 : _ThesisExpectedTypes.type_444.{u} := by exact @HiddenMonotonicity.TransformerDC.productSplit_convex_composition.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.productSplit_convex_composition
  let expected ← getConstInfo `_ThesisExactChecks.target_444
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.productSplit_convex_composition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.productSplit_convex_composition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PolarizedProductDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.productSplit_convex_composition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_444) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.productSplit_convex_composition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.productSplit_convex_composition"
#check @HiddenMonotonicity.TransformerDC.productSplit_convex_composition
#print axioms _ThesisExactChecks.target_444

section
universe u
def _ThesisExpectedTypes.type_445 : Prop := (∀ {E : Type u} [Preorder E] (s : Set E) (A B C D : E → ℝ), MonotoneOn A s → MonotoneOn B s → MonotoneOn C s → MonotoneOn D s → (∀ x ∈ s, 0 ≤ A x) → (∀ x ∈ s, 0 ≤ B x) → (∀ x ∈ s, 0 ≤ C x) → (∀ x ∈ s, 0 ≤ D x) → MonotoneOn (fun x => HiddenMonotonicity.TransformerDC.productSplit ((A x, B x), (C x, D x))) s)
theorem _ThesisExactChecks.target_445 : _ThesisExpectedTypes.type_445.{u} := by exact @HiddenMonotonicity.TransformerDC.productSplit_monotone_composition.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.productSplit_monotone_composition
  let expected ← getConstInfo `_ThesisExactChecks.target_445
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.productSplit_monotone_composition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.productSplit_monotone_composition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PolarizedProductDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.productSplit_monotone_composition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_445) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.productSplit_monotone_composition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.productSplit_monotone_composition"
#check @HiddenMonotonicity.TransformerDC.productSplit_monotone_composition
#print axioms _ThesisExactChecks.target_445

section
def _ThesisExpectedTypes.type_446 : Prop := (∀ ε : ℝ, 0 < ε → ∀ z : ℝ, HasDerivAt (HiddenMonotonicity.SmoothDC.inverseSqrtExtension ε) (HiddenMonotonicity.SmoothDC.inverseSqrtExtensionDeriv ε z) z)
theorem _ThesisExactChecks.target_446 : _ThesisExpectedTypes.type_446 := by exact @HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt
  let expected ← getConstInfo `_ThesisExactChecks.target_446
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_446) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt"
#check @HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt
#print axioms _ThesisExactChecks.target_446

section
def _ThesisExpectedTypes.type_447 : Prop := (∀ ε : ℝ, 0 < ε → ConvexOn ℝ Set.univ (HiddenMonotonicity.SmoothDC.inverseSqrtExtension ε))
theorem _ThesisExactChecks.target_447 : _ThesisExpectedTypes.type_447 := by exact @HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex
  let expected ← getConstInfo `_ThesisExactChecks.target_447
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_447) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex"
#check @HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex
#print axioms _ThesisExactChecks.target_447

section
def _ThesisExpectedTypes.type_448 : Prop := (∀ ε : ℝ, 0 < ε → ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z).1) ∧ ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z).2))
theorem _ThesisExactChecks.target_448 : _ThesisExpectedTypes.type_448 := by exact @HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex
  let expected ← getConstInfo `_ThesisExactChecks.target_448
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_448) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex"
#check @HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex
#print axioms _ThesisExactChecks.target_448

section
def _ThesisExpectedTypes.type_449 : Prop := (∀ ε : ℝ, 0 < ε → Monotone (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε))
theorem _ThesisExactChecks.target_449 : _ThesisExpectedTypes.type_449 := by exact @HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone
  let expected ← getConstInfo `_ThesisExactChecks.target_449
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_449) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone"
#check @HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone
#print axioms _ThesisExactChecks.target_449

section
def _ThesisExpectedTypes.type_450 : Prop := (∀ ε : ℝ, 0 < ε → ∀ z : ℝ × ℝ, 0 ≤ z → 0 ≤ HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z)
theorem _ThesisExactChecks.target_450 : _ThesisExpectedTypes.type_450 := by exact @HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg
  let expected ← getConstInfo `_ThesisExactChecks.target_450
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_450) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg"
#check @HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg
#print axioms _ThesisExactChecks.target_450

section
def _ThesisExpectedTypes.type_451 : Prop := (∀ ε : ℝ, 0 < ε → ∀ z : ℝ × ℝ, 0 ≤ z.1 - z.2 → (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z).1 - (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z).2 = (Real.sqrt (ε + (z.1 - z.2)))⁻¹)
theorem _ThesisExactChecks.target_451 : _ThesisExpectedTypes.type_451 := by exact @HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference
  let expected ← getConstInfo `_ThesisExactChecks.target_451
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_451) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference"
#check @HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference
#print axioms _ThesisExactChecks.target_451

section
def _ThesisExpectedTypes.type_452 : Prop := (∀ ε : ℝ, 0 < ε → HiddenMonotonicity.SmoothDC.inverseSqrtSlope ε = 1 / (2 * ε ^ (3 / 2 : ℝ)))
theorem _ThesisExactChecks.target_452 : _ThesisExpectedTypes.type_452 := by exact @HiddenMonotonicity.SmoothDC.inverseSqrtSlope_eq
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.inverseSqrtSlope_eq
  let expected ← getConstInfo `_ThesisExactChecks.target_452
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtSlope_eq"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.inverseSqrtSlope_eq | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtSlope_eq"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_452) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.inverseSqrtSlope_eq: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtSlope_eq"
#check @HiddenMonotonicity.SmoothDC.inverseSqrtSlope_eq
#print axioms _ThesisExactChecks.target_452

section
def _ThesisExpectedTypes.type_453 : Prop := (∀ ε : ℝ, 0 < ε → Monotone (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε) ∧ ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z).1) ∧ ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z).2) ∧ (∀ z : ℝ × ℝ, 0 ≤ z → 0 ≤ HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z) ∧ (∀ z : ℝ × ℝ, 0 ≤ z.1 - z.2 → (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z).1 - (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z).2 = (Real.sqrt (ε + (z.1 - z.2)))⁻¹))
theorem _ThesisExactChecks.target_453 : _ThesisExpectedTypes.type_453 := by exact @HiddenMonotonicity.SmoothDC.inverseSqrtPair_properties
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.inverseSqrtPair_properties
  let expected ← getConstInfo `_ThesisExactChecks.target_453
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_properties"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.inverseSqrtPair_properties | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_properties"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_453) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.inverseSqrtPair_properties: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_properties"
#check @HiddenMonotonicity.SmoothDC.inverseSqrtPair_properties
#print axioms _ThesisExactChecks.target_453

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_454 : Prop := (∀ c : ℝ, value (constPair c) = c)
theorem _ThesisExactChecks.target_454 : _ThesisExpectedTypes.type_454 := by exact @HiddenMonotonicity.TransformerDC.value_constPair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.value_constPair
  let expected ← getConstInfo `_ThesisExactChecks.target_454
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.value_constPair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.value_constPair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.value_constPair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_454) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.value_constPair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.value_constPair"
#check @HiddenMonotonicity.TransformerDC.value_constPair
#print axioms _ThesisExactChecks.target_454

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_455 : Prop := (∀ p q : ℝ × ℝ, value (addPair p q) = value p + value q)
theorem _ThesisExactChecks.target_455 : _ThesisExpectedTypes.type_455 := by exact @HiddenMonotonicity.TransformerDC.value_addPair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.value_addPair
  let expected ← getConstInfo `_ThesisExactChecks.target_455
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.value_addPair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.value_addPair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.value_addPair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_455) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.value_addPair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.value_addPair"
#check @HiddenMonotonicity.TransformerDC.value_addPair
#print axioms _ThesisExactChecks.target_455

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_456 : Prop := (∀ (c : ℝ) (p : ℝ × ℝ), value (scalePair c p) = c * value p)
theorem _ThesisExactChecks.target_456 : _ThesisExpectedTypes.type_456 := by exact @HiddenMonotonicity.TransformerDC.value_scalePair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.value_scalePair
  let expected ← getConstInfo `_ThesisExactChecks.target_456
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.value_scalePair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.value_scalePair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.value_scalePair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_456) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.value_scalePair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.value_scalePair"
#check @HiddenMonotonicity.TransformerDC.value_scalePair
#print axioms _ThesisExactChecks.target_456

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_457 : Prop := (∀ p q : ℝ × ℝ, value (mulPair p q) = value p * value q)
theorem _ThesisExactChecks.target_457 : _ThesisExpectedTypes.type_457 := by exact @HiddenMonotonicity.TransformerDC.value_mulPair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.value_mulPair
  let expected ← getConstInfo `_ThesisExactChecks.target_457
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.value_mulPair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.value_mulPair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.value_mulPair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_457) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.value_mulPair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.value_mulPair"
#check @HiddenMonotonicity.TransformerDC.value_mulPair
#print axioms _ThesisExactChecks.target_457

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_458 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E] {s : Set E}, Convex ℝ s → ∀ c : ℝ, Regular s (fun _ : E => constPair c))
theorem _ThesisExactChecks.target_458 : _ThesisExpectedTypes.type_458.{u} := by exact @HiddenMonotonicity.TransformerDC.Regular.const.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Regular.const
  let expected ← getConstInfo `_ThesisExactChecks.target_458
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Regular.const"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Regular.const | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Regular.const"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_458) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Regular.const: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Regular.const"
#check @HiddenMonotonicity.TransformerDC.Regular.const
#print axioms _ThesisExactChecks.target_458

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_459 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E] {s : Set E}, ∀ {f : E → ℝ × ℝ}, Regular s f → ∀ c : ℝ, Regular s (fun x => scalePair c (f x)))
theorem _ThesisExactChecks.target_459 : _ThesisExpectedTypes.type_459.{u} := by exact @HiddenMonotonicity.TransformerDC.Regular.scale.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Regular.scale
  let expected ← getConstInfo `_ThesisExactChecks.target_459
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Regular.scale"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Regular.scale | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Regular.scale"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_459) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Regular.scale: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Regular.scale"
#check @HiddenMonotonicity.TransformerDC.Regular.scale
#print axioms _ThesisExactChecks.target_459

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_460 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E] {s : Set E}, ∀ {f g : E → ℝ × ℝ}, Regular s f → Regular s g → Regular s (fun x => mulPair (f x) (g x)))
theorem _ThesisExactChecks.target_460 : _ThesisExpectedTypes.type_460.{u} := by exact @HiddenMonotonicity.TransformerDC.Regular.mul.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Regular.mul
  let expected ← getConstInfo `_ThesisExactChecks.target_460
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Regular.mul"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Regular.mul | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Regular.mul"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_460) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Regular.mul: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Regular.mul"
#check @HiddenMonotonicity.TransformerDC.Regular.mul
#print axioms _ThesisExactChecks.target_460

section
universe u v
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_461 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E] {s : Set E}, ∀ {ι : Type v} (t : Finset ι) (f : ι → E → ℝ × ℝ), Convex ℝ s → (∀ i ∈ t, Regular s (f i)) → Regular s (fun x => ∑ i ∈ t, f i x))
theorem _ThesisExactChecks.target_461 : _ThesisExpectedTypes.type_461.{u, v} := by exact @HiddenMonotonicity.TransformerDC.Regular.finset_sum.{u, v}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Regular.finset_sum
  let expected ← getConstInfo `_ThesisExactChecks.target_461
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Regular.finset_sum"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Regular.finset_sum | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Regular.finset_sum"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_461) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Regular.finset_sum: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Regular.finset_sum"
#check @HiddenMonotonicity.TransformerDC.Regular.finset_sum
#print axioms _ThesisExactChecks.target_461

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_462 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E] {s : Set E}, ∀ {f : E → ℝ × ℝ}, Regular s f → ∀ φ : (ℝ × ℝ) → ℝ × ℝ, ConvexOn ℝ Set.univ (fun z => (φ z).1) → ConvexOn ℝ Set.univ (fun z => (φ z).2) → Monotone φ → (∀ z, 0 ≤ z → 0 ≤ φ z) → Regular s (fun x => φ (f x)))
theorem _ThesisExactChecks.target_462 : _ThesisExpectedTypes.type_462.{u} := by exact @HiddenMonotonicity.TransformerDC.Regular.scalar_comp.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Regular.scalar_comp
  let expected ← getConstInfo `_ThesisExactChecks.target_462
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Regular.scalar_comp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Regular.scalar_comp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Regular.scalar_comp"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_462) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Regular.scalar_comp: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Regular.scalar_comp"
#check @HiddenMonotonicity.TransformerDC.Regular.scalar_comp
#print axioms _ThesisExactChecks.target_462

section
universe u v
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_463 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E] {s : Set E}, ∀ {ι : Type v} (φ : ((ι → ℝ) × (ι → ℝ)) → ℝ × ℝ), ConvexOn ℝ Set.univ (fun z => (φ z).1) → ConvexOn ℝ Set.univ (fun z => (φ z).2) → Monotone φ → (∀ z, 0 ≤ z → 0 ≤ φ z) → Convex ℝ s → ∀ f : ι → E → ℝ × ℝ, (∀ i, Regular s (f i)) → Regular s (fun x => φ ((fun i => (f i x).1), (fun i => (f i x).2))))
theorem _ThesisExactChecks.target_463 : _ThesisExpectedTypes.type_463.{u, v} := by exact @HiddenMonotonicity.TransformerDC.Regular.vector_comp.{u, v}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Regular.vector_comp
  let expected ← getConstInfo `_ThesisExactChecks.target_463
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Regular.vector_comp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Regular.vector_comp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Regular.vector_comp"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_463) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Regular.vector_comp: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Regular.vector_comp"
#check @HiddenMonotonicity.TransformerDC.Regular.vector_comp
#print axioms _ThesisExactChecks.target_463

section
def _ThesisExpectedTypes.type_464 : Prop := (∀ {d : ℕ} (v : Fin d → ℝ), 0 ≤ HiddenMonotonicity.TransformerDC.layerVariance v)
theorem _ThesisExactChecks.target_464 : _ThesisExpectedTypes.type_464 := by exact @HiddenMonotonicity.TransformerDC.layerVariance_nonnegative
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.layerVariance_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_464
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.layerVariance_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.layerVariance_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.layerVariance_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_464) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.layerVariance_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.layerVariance_nonnegative"
#check @HiddenMonotonicity.TransformerDC.layerVariance_nonnegative
#print axioms _ThesisExactChecks.target_464

section
def _ThesisExpectedTypes.type_465 : Prop := (∀ {d : ℕ} (xs : Fin d → ℝ × ℝ), HiddenMonotonicity.TransformerDC.value (HiddenMonotonicity.TransformerDC.variancePair xs) = HiddenMonotonicity.TransformerDC.layerVariance (fun i => HiddenMonotonicity.TransformerDC.value (xs i)))
theorem _ThesisExactChecks.target_465 : _ThesisExpectedTypes.type_465 := by exact @HiddenMonotonicity.TransformerDC.value_variancePair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.value_variancePair
  let expected ← getConstInfo `_ThesisExactChecks.target_465
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.value_variancePair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.value_variancePair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.value_variancePair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_465) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.value_variancePair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.value_variancePair"
#check @HiddenMonotonicity.TransformerDC.value_variancePair
#print axioms _ThesisExactChecks.target_465

section
def _ThesisExpectedTypes.type_466 : Prop := (∀ {d : ℕ} (ε : ℝ), 0 < ε → ∀ (γ β : Fin d → ℝ) (xs : Fin d → ℝ × ℝ) (i : Fin d), HiddenMonotonicity.TransformerDC.value (HiddenMonotonicity.TransformerDC.layerNormPair ε γ β xs i) = HiddenMonotonicity.TransformerDC.layerNorm ε γ β (fun j => HiddenMonotonicity.TransformerDC.value (xs j)) i)
theorem _ThesisExactChecks.target_466 : _ThesisExpectedTypes.type_466 := by exact @HiddenMonotonicity.TransformerDC.layerNormPair_exact
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.layerNormPair_exact
  let expected ← getConstInfo `_ThesisExactChecks.target_466
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.layerNormPair_exact"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.layerNormPair_exact | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.layerNormPair_exact"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_466) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.layerNormPair_exact: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.layerNormPair_exact"
#check @HiddenMonotonicity.TransformerDC.layerNormPair_exact
#print axioms _ThesisExactChecks.target_466

section
universe u
def _ThesisExpectedTypes.type_467 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E] {d : ℕ} (s : Set E), Convex ℝ s → ∀ ε : ℝ, 0 < ε → ∀ (γ β : Fin d → ℝ) (f : Fin d → E → ℝ × ℝ), (∀ i, HiddenMonotonicity.TransformerDC.Regular s (f i)) → ∀ i : Fin d, HiddenMonotonicity.TransformerDC.Regular s (fun x => HiddenMonotonicity.TransformerDC.layerNormPair ε γ β (fun j => f j x) i))
theorem _ThesisExactChecks.target_467 : _ThesisExpectedTypes.type_467.{u} := by exact @HiddenMonotonicity.TransformerDC.layerNormPair_regular.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.layerNormPair_regular
  let expected ← getConstInfo `_ThesisExactChecks.target_467
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.layerNormPair_regular"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.layerNormPair_regular | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.layerNormPair_regular"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_467) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.layerNormPair_regular: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.layerNormPair_regular"
#check @HiddenMonotonicity.TransformerDC.layerNormPair_regular
#print axioms _ThesisExactChecks.target_467

section
universe u v
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_468 : Prop := (∀ {E : Type u} {ι : Type v} [AddCommGroup E] [Module ℝ E] (s : Set E), Convex ℝ s → ∀ φ : ((ι → ℝ) × (ι → ℝ)) → ℝ, ConvexOn ℝ (Set.Ici (0 : (ι → ℝ) × (ι → ℝ))) φ → MonotoneOn φ (Set.Ici (0 : (ι → ℝ) × (ι → ℝ))) → ∀ p q : E → ι → ℝ, (∀ i, ConvexOn ℝ s (fun x => p x i)) → (∀ i, ConvexOn ℝ s (fun x => q x i)) → (∀ x ∈ s, 0 ≤ p x) → (∀ x ∈ s, 0 ≤ q x) → ConvexOn ℝ s (fun x => φ (p x, q x)))
theorem _ThesisExactChecks.target_468 : _ThesisExpectedTypes.type_468.{u, v} := by exact @HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on.{u, v}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on
  let expected ← getConstInfo `_ThesisExactChecks.target_468
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerConvexInput do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_468) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on"
#check @HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on
#print axioms _ThesisExactChecks.target_468

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_469 : Prop := (∀ {ι : Type u} (φ : ((ι → ℝ) × (ι → ℝ)) → ℝ), ConvexOn ℝ (Set.Ici (0 : (ι → ℝ) × (ι → ℝ))) φ → MonotoneOn φ (Set.Ici (0 : (ι → ℝ) × (ι → ℝ))) → ConvexOn ℝ Set.univ (fun x : ι → ℝ => φ ((fun i => max (x i) 0), (fun i => max (-x i) 0))))
theorem _ThesisExactChecks.target_469 : _ThesisExpectedTypes.type_469.{u} := by exact @HiddenMonotonicity.TransformerDC.convex_signed_input_lift.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.convex_signed_input_lift
  let expected ← getConstInfo `_ThesisExactChecks.target_469
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.convex_signed_input_lift"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.convex_signed_input_lift | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerConvexInput do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.convex_signed_input_lift"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_469) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.convex_signed_input_lift: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.convex_signed_input_lift"
#check @HiddenMonotonicity.TransformerDC.convex_signed_input_lift
#print axioms _ThesisExactChecks.target_469

section
universe u
def _ThesisExpectedTypes.type_470 : Prop := (∀ {ι : Type u} (e : HiddenMonotonicity.TransformerDC.Expr ι) (x : ι → ℝ × ℝ), HiddenMonotonicity.TransformerDC.value (e.splitEval x) = e.eval (fun i => HiddenMonotonicity.TransformerDC.value (x i)))
theorem _ThesisExactChecks.target_470 : _ThesisExpectedTypes.type_470.{u} := by exact @HiddenMonotonicity.TransformerDC.Expr.splitEval_exact.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Expr.splitEval_exact
  let expected ← getConstInfo `_ThesisExactChecks.target_470
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Expr.splitEval_exact"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Expr.splitEval_exact | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerExpr do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Expr.splitEval_exact"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_470) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Expr.splitEval_exact: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Expr.splitEval_exact"
#check @HiddenMonotonicity.TransformerDC.Expr.splitEval_exact
#print axioms _ThesisExactChecks.target_470

section
universe u v
def _ThesisExpectedTypes.type_471 : Prop := (∀ {ι : Type u} {E : Type v} [AddCommGroup E] [Module ℝ E] [Preorder E] (e : HiddenMonotonicity.TransformerDC.Expr ι) (s : Set E), Convex ℝ s → ∀ (f : ι → E → ℝ × ℝ), (∀ i, HiddenMonotonicity.TransformerDC.Regular s (f i)) → HiddenMonotonicity.TransformerDC.Regular s (fun x => e.splitEval (fun i => f i x)))
theorem _ThesisExactChecks.target_471 : _ThesisExpectedTypes.type_471.{u, v} := by exact @HiddenMonotonicity.TransformerDC.Expr.splitEval_regular.{u, v}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Expr.splitEval_regular
  let expected ← getConstInfo `_ThesisExactChecks.target_471
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Expr.splitEval_regular"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Expr.splitEval_regular | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerExpr do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Expr.splitEval_regular"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_471) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Expr.splitEval_regular: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Expr.splitEval_regular"
#check @HiddenMonotonicity.TransformerDC.Expr.splitEval_regular
#print axioms _ThesisExactChecks.target_471

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_472 : Prop := (∀ {t d : ℕ} {ι : Type u} (h : TransformerHead t d) (x : Fin t → Fin d → Expr ι) (v : ι → ℝ) (q : Fin t) (i : Fin d), (h.compile x q i).eval v = h.eval (fun a b => (x a b).eval v) q i)
theorem _ThesisExactChecks.target_472 : _ThesisExpectedTypes.type_472.{u} := by exact @HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile
  let expected ← getConstInfo `_ThesisExactChecks.target_472
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_472) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile"
#check @HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile
#print axioms _ThesisExactChecks.target_472

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_473 : Prop := (∀ {t d : ℕ} {ι : Type u} (b : TransformerBlock t d) (x : Fin t → Fin d → Expr ι) (v : ι → ℝ) (q : Fin t) (i : Fin d), (b.compile x q i).eval v = b.eval (fun a c => (x a c).eval v) q i)
theorem _ThesisExactChecks.target_473 : _ThesisExpectedTypes.type_473.{u} := by exact @HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile
  let expected ← getConstInfo `_ThesisExactChecks.target_473
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_473) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile"
#check @HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile
#print axioms _ThesisExactChecks.target_473

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_474 : Prop := (∀ {t d : ℕ} {ι : Type u} (bs : List (TransformerBlock t d)) (x : Fin t → Fin d → Expr ι) (v : ι → ℝ) (q : Fin t) (i : Fin d), (compileTransformerBlocks bs x q i).eval v = evalTransformerBlocks bs (fun a c => (x a c).eval v) q i)
theorem _ThesisExactChecks.target_474 : _ThesisExpectedTypes.type_474.{u} := by exact @HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks
  let expected ← getConstInfo `_ThesisExactChecks.target_474
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_474) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks"
#check @HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks
#print axioms _ThesisExactChecks.target_474

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_475 : Prop := (∀ {t d : ℕ} {ι : Type u} (p : Option (TransformerNorm d)) (x : Fin t → Fin d → Expr ι) (v : ι → ℝ) (q : Fin t) (i : Fin d), (compileOptionalTransformerNorm p x q i).eval v = evalOptionalTransformerNorm p (fun a c => (x a c).eval v) q i)
theorem _ThesisExactChecks.target_475 : _ThesisExpectedTypes.type_475.{u} := by exact @HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm
  let expected ← getConstInfo `_ThesisExactChecks.target_475
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_475) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm"
#check @HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm
#print axioms _ThesisExactChecks.target_475

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_476 : Prop := (∀ {t d o : ℕ} {ι : Type u} (net : Transformer t d o) (x : Fin t → Fin d → Expr ι) (v : ι → ℝ) (i : Fin o), (net.compile x i).eval v = net.eval (fun p => (x p.1 p.2).eval v) i)
theorem _ThesisExactChecks.target_476 : _ThesisExpectedTypes.type_476.{u} := by exact @HiddenMonotonicity.TransformerDC.Transformer.eval_compile.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.eval_compile
  let expected ← getConstInfo `_ThesisExactChecks.target_476
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval_compile"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.eval_compile | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval_compile"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_476) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.eval_compile: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval_compile"
#check @HiddenMonotonicity.TransformerDC.Transformer.eval_compile
#print axioms _ThesisExactChecks.target_476

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_477 : Prop := (∀ {t d o : ℕ} (net : Transformer t d o) (x : Fin t × Fin d → ℝ) (i : Fin o), (net.syntax i).eval x = net.eval x i)
theorem _ThesisExactChecks.target_477 : _ThesisExpectedTypes.type_477 := by exact @HiddenMonotonicity.TransformerDC.Transformer.eval_syntax
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.eval_syntax
  let expected ← getConstInfo `_ThesisExactChecks.target_477
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval_syntax"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.eval_syntax | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval_syntax"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_477) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.eval_syntax: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval_syntax"
#check @HiddenMonotonicity.TransformerDC.Transformer.eval_syntax
#print axioms _ThesisExactChecks.target_477

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_478 := (∀ {t d : ℕ} (h : TransformerHead t d), (Fin t → Fin d → ℝ) → Fin t → Fin d → ℝ)
noncomputable def _ThesisExactChecks.target_478 : _ThesisExpectedTypes.type_478 := by exact @HiddenMonotonicity.TransformerDC.TransformerHead.eval
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.TransformerHead.eval
  let expected ← getConstInfo `_ThesisExactChecks.target_478
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.TransformerHead.eval"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.TransformerHead.eval | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.TransformerHead.eval"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_478) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.TransformerHead.eval: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.TransformerHead.eval"
#check @HiddenMonotonicity.TransformerDC.TransformerHead.eval
#print axioms _ThesisExactChecks.target_478

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_479 := (∀ {t d : ℕ} (b : TransformerBlock t d), (Fin t → Fin d → ℝ) → Fin t → Fin d → ℝ)
noncomputable def _ThesisExactChecks.target_479 : _ThesisExpectedTypes.type_479 := by exact @HiddenMonotonicity.TransformerDC.TransformerBlock.eval
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.TransformerBlock.eval
  let expected ← getConstInfo `_ThesisExactChecks.target_479
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.TransformerBlock.eval"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.TransformerBlock.eval | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.TransformerBlock.eval"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_479) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.TransformerBlock.eval: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.TransformerBlock.eval"
#check @HiddenMonotonicity.TransformerDC.TransformerBlock.eval
#print axioms _ThesisExactChecks.target_479

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_480 := (∀ {t d o : ℕ} (net : Transformer t d o), (Fin t × Fin d → ℝ) → Fin o → ℝ)
noncomputable def _ThesisExactChecks.target_480 : _ThesisExpectedTypes.type_480 := by exact @HiddenMonotonicity.TransformerDC.Transformer.eval
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.eval
  let expected ← getConstInfo `_ThesisExactChecks.target_480
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.eval | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_480) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.eval: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval"
#check @HiddenMonotonicity.TransformerDC.Transformer.eval
#print axioms _ThesisExactChecks.target_480

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_481 := (∀ {t d o : ℕ} (net : Transformer t d o), Fin o → Expr (Fin t × Fin d))
noncomputable def _ThesisExactChecks.target_481 : _ThesisExpectedTypes.type_481 := by exact @HiddenMonotonicity.TransformerDC.Transformer.syntax
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.syntax
  let expected ← getConstInfo `_ThesisExactChecks.target_481
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.syntax"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.syntax | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.syntax"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_481) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.syntax: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.syntax"
#check @HiddenMonotonicity.TransformerDC.Transformer.syntax
#print axioms _ThesisExactChecks.target_481

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_482 : Prop := (∀ {t d o : ℕ} (net : Transformer t d o) (x : DoubledInput (Fin t × Fin d)) (i : Fin o),
  (net.decompose x i).1 - (net.decompose x i).2 = net.eval (x.1 - x.2) i)
theorem _ThesisExactChecks.target_482 : _ThesisExpectedTypes.type_482 := by exact @HiddenMonotonicity.TransformerDC.Transformer.decompose_exact
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.decompose_exact
  let expected ← getConstInfo `_ThesisExactChecks.target_482
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.decompose_exact"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.decompose_exact | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerCorrectness do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.decompose_exact"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_482) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.decompose_exact: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.decompose_exact"
#check @HiddenMonotonicity.TransformerDC.Transformer.decompose_exact
#print axioms _ThesisExactChecks.target_482

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_483 : Prop := (∀ {t d o : ℕ} (net : Transformer t d o) (i : Fin o),
  Regular (Set.Ici (0 : DoubledInput (Fin t × Fin d))) (fun x => net.decompose x i))
theorem _ThesisExactChecks.target_483 : _ThesisExpectedTypes.type_483 := by exact @HiddenMonotonicity.TransformerDC.Transformer.decompose_regular
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.decompose_regular
  let expected ← getConstInfo `_ThesisExactChecks.target_483
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.decompose_regular"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.decompose_regular | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerCorrectness do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.decompose_regular"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_483) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.decompose_regular: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.decompose_regular"
#check @HiddenMonotonicity.TransformerDC.Transformer.decompose_regular
#print axioms _ThesisExactChecks.target_483

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_484 : Prop := (∀ {t d o : ℕ} (net : Transformer t d o),
  MonotoneOn net.decompose (Set.Ici (0 : DoubledInput (Fin t × Fin d))) ∧
  (∀ i, ConvexOn ℝ (Set.Ici (0 : DoubledInput (Fin t × Fin d))) (fun x => (net.decompose x i).1)) ∧
  (∀ i, ConvexOn ℝ (Set.Ici (0 : DoubledInput (Fin t × Fin d))) (fun x => (net.decompose x i).2)) ∧
  (∀ x, 0 ≤ x → 0 ≤ net.decompose x) ∧
  ∀ x i, (net.decompose x i).1 - (net.decompose x i).2 = net.eval (x.1 - x.2) i)
theorem _ThesisExactChecks.target_484 : _ThesisExpectedTypes.type_484 := by exact @HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition
  let expected ← getConstInfo `_ThesisExactChecks.target_484
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerCorrectness do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_484) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition"
#check @HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition
#print axioms _ThesisExactChecks.target_484

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_485 : Prop := (∀ {t d o : ℕ} (net : Transformer t d o),
  (∀ i, ConvexOn ℝ Set.univ (fun x : Fin t × Fin d → ℝ => (net.rawDecompose x i).1)) ∧
  (∀ i, ConvexOn ℝ Set.univ (fun x : Fin t × Fin d → ℝ => (net.rawDecompose x i).2)) ∧
  (∀ x, 0 ≤ net.rawDecompose x) ∧
  ∀ x i, (net.rawDecompose x i).1 - (net.rawDecompose x i).2 = net.eval x i)
theorem _ThesisExactChecks.target_485 : _ThesisExpectedTypes.type_485 := by exact @HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition
  let expected ← getConstInfo `_ThesisExactChecks.target_485
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerCorrectness do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_485) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition"
#check @HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition
#print axioms _ThesisExactChecks.target_485

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_486 : Prop := (∀ {ι : Type u} (e : Expr ι), Regular (Set.Ici (0 : DoubledInput ι)) e.decompose)
theorem _ThesisExactChecks.target_486 : _ThesisExpectedTypes.type_486.{u} := by exact @HiddenMonotonicity.TransformerDC.Expr.decompose_regular.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Expr.decompose_regular
  let expected ← getConstInfo `_ThesisExactChecks.target_486
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Expr.decompose_regular"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Expr.decompose_regular | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerExprProperties do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Expr.decompose_regular"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_486) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Expr.decompose_regular: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Expr.decompose_regular"
#check @HiddenMonotonicity.TransformerDC.Expr.decompose_regular
#print axioms _ThesisExactChecks.target_486

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_487 : Prop := (∀ {ι : Type u} (e : Expr ι) (x : DoubledInput ι), value (e.decompose x) = e.eval (x.1 - x.2))
theorem _ThesisExactChecks.target_487 : _ThesisExpectedTypes.type_487.{u} := by exact @HiddenMonotonicity.TransformerDC.Expr.decompose_exact.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Expr.decompose_exact
  let expected ← getConstInfo `_ThesisExactChecks.target_487
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Expr.decompose_exact"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Expr.decompose_exact | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerExprProperties do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Expr.decompose_exact"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_487) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Expr.decompose_exact: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Expr.decompose_exact"
#check @HiddenMonotonicity.TransformerDC.Expr.decompose_exact
#print axioms _ThesisExactChecks.target_487

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_488 : Prop := (∀ {ι : Type u} (e : Expr ι),
  ConvexOn ℝ Set.univ (fun x : ι → ℝ => (e.rawDecompose x).1) ∧
  ConvexOn ℝ Set.univ (fun x : ι → ℝ => (e.rawDecompose x).2))
theorem _ThesisExactChecks.target_488 : _ThesisExpectedTypes.type_488.{u} := by exact @HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex
  let expected ← getConstInfo `_ThesisExactChecks.target_488
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerExprProperties do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_488) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex"
#check @HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex
#print axioms _ThesisExactChecks.target_488

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_489 : Prop := (∀ {ι : Type u} (e : Expr ι) (x : ι → ℝ), value (e.rawDecompose x) = e.eval x)
theorem _ThesisExactChecks.target_489 : _ThesisExpectedTypes.type_489.{u} := by exact @HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact
  let expected ← getConstInfo `_ThesisExactChecks.target_489
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerExprProperties do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_489) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact"
#check @HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact
#print axioms _ThesisExactChecks.target_489

set_option maxHeartbeats 0
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut records : Array Json := #[]
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[index.toNat]!
    unless modName.toString.startsWith "HiddenMonotonicity" || modName.toString.startsWith "Thesis" do continue
    let .thmInfo _ := info | continue
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unapproved axiom {axiomName} in {name}"
    let typeText ← liftTermElabM do return (← Lean.Meta.ppExpr info.type).pretty
    records := records.push <| Json.mkObj [
      ("declaration", toJson name.toString), ("module", toJson modName.toString),
      ("type", toJson typeText), ("universes", toJson (info.levelParams.map Name.toString)),
      ("axioms", toJson (axioms.map Name.toString))]
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/verification/commit-1f886dd/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

