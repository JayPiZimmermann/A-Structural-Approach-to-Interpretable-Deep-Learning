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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/structural-explainability-thesis/reports/verification/current/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

