import HiddenMonotonicity.MultivariateMonotoneDCLift
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_0 : Prop := (∀ {ι : Type u} (f : (ι → ℝ) → ℝ), (∀ a v : ι → ℝ, ConvexOn ℝ Set.univ (fun t : ℝ => f (fun j => a j + t * v j))) → ConvexOn ℝ Set.univ f)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0.{u} := by exact @HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MultivariateMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines"
#check @HiddenMonotonicity.SoftmaxDC.convex_from_affine_lines
#print axioms _ThesisExactChecks.target_0

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_1 : Prop := (∀ {ι : Type u} (f : (ι → ℝ) → ℝ) (D : (ι → ℝ) → (ι → ℝ) → ℝ), (∀ (a v : ι → ℝ) (t : ℝ), HasDerivAt (fun s : ℝ => f (fun j => a j + s * v j)) (D (fun j => a j + t * v j) v) t) → (∀ z v : ι → ℝ, (∀ j, 0 ≤ v j) → 0 ≤ D z v) → Monotone f)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1.{u} := by exact @HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MultivariateMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv"
#check @HiddenMonotonicity.SoftmaxDC.monotone_from_affine_line_deriv
#print axioms _ThesisExactChecks.target_1

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_2 : Prop := (∀ {ι : Type u} [Fintype ι] (P : (ι → ℝ) → ℝ) (L c : ℝ), ConvexOn ℝ Set.univ P → ConvexOn ℝ Set.univ (HiddenMonotonicity.SoftmaxDC.multivariateLift P L c))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2.{u} := by exact @HiddenMonotonicity.SoftmaxDC.multivariateLift_convex.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.multivariateLift_convex
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_convex"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.multivariateLift_convex | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MultivariateMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_convex"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.multivariateLift_convex: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_convex"
#check @HiddenMonotonicity.SoftmaxDC.multivariateLift_convex
#print axioms _ThesisExactChecks.target_2

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_3 : Prop := (∀ {ι : Type u} [Fintype ι] (P : (ι → ℝ) → ℝ) (L c : ℝ), Monotone P → Monotone (fun x : ι → ℝ => L * (∑ j, x j) - P x) → Monotone (HiddenMonotonicity.SoftmaxDC.multivariateLift P L c))
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3.{u} := by exact @HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MultivariateMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone"
#check @HiddenMonotonicity.SoftmaxDC.multivariateLift_monotone
#print axioms _ThesisExactChecks.target_3

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_4 : Prop := (∀ {ι : Type u} [Fintype ι] (P Q f : (ι → ℝ) → ℝ) (L c : ℝ), (∀ x, P x - Q x = f x) → ∀ z : (ι → ℝ) × (ι → ℝ), HiddenMonotonicity.SoftmaxDC.multivariateLift P L c z - HiddenMonotonicity.SoftmaxDC.multivariateLift Q L c z = f (z.1 - z.2))
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4.{u} := by exact @HiddenMonotonicity.SoftmaxDC.multivariateLift_difference.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.multivariateLift_difference
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_difference"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.multivariateLift_difference | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MultivariateMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_difference"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.multivariateLift_difference: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_difference"
#check @HiddenMonotonicity.SoftmaxDC.multivariateLift_difference
#print axioms _ThesisExactChecks.target_4

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_5 : Prop := (∀ {ι : Type u} [Fintype ι] (P : (ι → ℝ) → ℝ) (L c : ℝ), Monotone (HiddenMonotonicity.SoftmaxDC.multivariateLift P L c) → c ≤ P 0 → ∀ z : (ι → ℝ) × (ι → ℝ), 0 ≤ z → 0 ≤ HiddenMonotonicity.SoftmaxDC.multivariateLift P L c z)
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5.{u} := by exact @HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MultivariateMonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative"
#check @HiddenMonotonicity.SoftmaxDC.multivariateLift_nonnegative
#print axioms _ThesisExactChecks.target_5

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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/softmax-dc/multivariate-lift-enforcement/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

