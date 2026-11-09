import HiddenMonotonicity.Convolution
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity HiddenMonotonicity.Convolution
def _ThesisExpectedTypes.type_0 : Prop := (∀ {ci co ip op taps : ℕ}
(K : Fin co → Fin ci → Fin taps → ℝ)
(stencil : Fin op → Fin taps → Option (Fin ip)) (x : Vec (ci*ip)),
applyKernel K stencil x = (kernelMatrix K stencil).mulVec x)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.Convolution.applyKernel_eq_mulVec
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Convolution.applyKernel_eq_mulVec
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Convolution.applyKernel_eq_mulVec"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Convolution.applyKernel_eq_mulVec | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Convolution do
    throwError "Defining module mismatch: HiddenMonotonicity.Convolution.applyKernel_eq_mulVec"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Convolution.applyKernel_eq_mulVec: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Convolution.applyKernel_eq_mulVec"
#check @HiddenMonotonicity.Convolution.applyKernel_eq_mulVec
#print axioms _ThesisExactChecks.target_0

section
open HiddenMonotonicity HiddenMonotonicity.Convolution
def _ThesisExpectedTypes.type_1 : Prop := (∀ {ci co ip op taps : ℕ}
(K : Fin co → Fin ci → Fin taps → ℝ)
(stencil : Fin op → Fin taps → Option (Fin ip)) (x : Vec (ci*ip)),
HasFDerivAt (applyKernel K stencil) (matrixCLM (kernelMatrix K stencil)) x)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Convolution do
    throwError "Defining module mismatch: HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt"
#check @HiddenMonotonicity.Convolution.applyKernel_hasFDerivAt
#print axioms _ThesisExactChecks.target_1

section
open HiddenMonotonicity HiddenMonotonicity.Convolution
def _ThesisExpectedTypes.type_2 : Prop := (∀ {ci co ip op taps : ℕ}
(K : Fin co → Fin ci → Fin taps → ℝ)
(stencil : Fin op → Fin taps → Option (Fin ip)) (b : Fin co → ℝ) (x : PairVec (ci*ip)),
HasFDerivAt (splitKernel K stencil b)
((preP (kernelMatrix (positiveKernel K) stencil) (kernelMatrix (negativeKernel K) stencil)).prod
(preN (kernelMatrix (positiveKernel K) stencil) (kernelMatrix (negativeKernel K) stencil))) x)
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Convolution do
    throwError "Defining module mismatch: HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt"
#check @HiddenMonotonicity.Convolution.splitKernel_hasFDerivAt
#print axioms _ThesisExactChecks.target_2

section
open HiddenMonotonicity HiddenMonotonicity.Convolution
def _ThesisExpectedTypes.type_3 : Prop := (∀ {ci co ip op taps : ℕ}
(K : Fin co → Fin ci → Fin taps → ℝ)
(stencil : Fin op → Fin taps → Option (Fin ip)) (b : Fin co → ℝ),
(∀ x, 0 ≤ x → 0 ≤ splitKernel K stencil b x) ∧
Monotone (splitKernel K stencil b) ∧
(∀ i, ConvexOn ℝ Set.univ (fun x => (splitKernel K stencil b x).1 i) ∧
ConvexOn ℝ Set.univ (fun x => (splitKernel K stencil b x).2 i)) ∧
(∀ x, (splitKernel K stencil b x).1-(splitKernel K stencil b x).2 =
applyKernel K stencil (x.1-x.2)+(fun u => b (unflat u).1)))
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @HiddenMonotonicity.Convolution.splitKernel_properties
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Convolution.splitKernel_properties
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Convolution.splitKernel_properties"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Convolution.splitKernel_properties | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Convolution do
    throwError "Defining module mismatch: HiddenMonotonicity.Convolution.splitKernel_properties"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Convolution.splitKernel_properties: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Convolution.splitKernel_properties"
#check @HiddenMonotonicity.Convolution.splitKernel_properties
#print axioms _ThesisExactChecks.target_3

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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/dc_decompose/master_thesis/reports/evidence/convolution/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

