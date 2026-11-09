import HiddenMonotonicity.AffineChunk
import HiddenMonotonicity.AffineReadout
import HiddenMonotonicity.Chunks
import HiddenMonotonicity.Core
import HiddenMonotonicity.Decomposition
import HiddenMonotonicity.MaxPool
import HiddenMonotonicity.NetworkDerivative
import HiddenMonotonicity.OriginalTrace
import HiddenMonotonicity.StabilizedBackward
import Thesis.Games
import Thesis.GeneralRegularization
import Thesis.ReferencePolicy
import Thesis.Regularization
import Thesis.RoutingSupport
import Thesis.StoppingDAGPaths
import Thesis.StoppingDAGVisits
import Thesis.StoppingDecomposition
import Thesis.Tropical
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_0 := (∀ {n : ℕ}, ℝ → Sensitivity n → Sensitivity n)
noncomputable def _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.shiftPair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.shiftPair
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.shiftPair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.shiftPair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.StabilizedBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.shiftPair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.shiftPair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.shiftPair"
#check @HiddenMonotonicity.shiftPair
#print axioms _ThesisExactChecks.target_0

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_1 := (∀ {n : ℕ}, Sensitivity n → Row n)
noncomputable def _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @HiddenMonotonicity.unified
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.unified
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.unified"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.unified | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.StabilizedBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.unified"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.unified: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.unified"
#check @HiddenMonotonicity.unified
#print axioms _ThesisExactChecks.target_1

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_2 : Prop := (∀ {n : ℕ} (α : ℝ) (s : Sensitivity n), (shiftPair α s).1+(shiftPair α s).2 = (1-2*α) • (s.1+s.2))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @HiddenMonotonicity.shiftPair_sum
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.shiftPair_sum
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.shiftPair_sum"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.shiftPair_sum | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.StabilizedBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.shiftPair_sum"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.shiftPair_sum: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.shiftPair_sum"
#check @HiddenMonotonicity.shiftPair_sum
#print axioms _ThesisExactChecks.target_2

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_3 : Prop := (∀ {n : ℕ} (α : ℝ) (s : Sensitivity n), unified (shiftPair α s)=unified s)
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @HiddenMonotonicity.unified_shift
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.unified_shift
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.unified_shift"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.unified_shift | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.StabilizedBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.unified_shift"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.unified_shift: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.unified_shift"
#check @HiddenMonotonicity.unified_shift
#print axioms _ThesisExactChecks.target_3

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_4 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (gate : Fin k → Bool) (s : Sensitivity k), unified (MaskedTrace.pull wp wn gate s)=(unified s).comp (MaskedTrace.signedMap wp wn gate)-(1/2 : ℝ) • ((s.1+s.2).comp (MaskedTrace.deadMap wp wn gate)))
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4 := by exact @HiddenMonotonicity.MaskedTrace.pull_unified
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaskedTrace.pull_unified
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaskedTrace.pull_unified"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaskedTrace.pull_unified | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.StabilizedBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.MaskedTrace.pull_unified"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaskedTrace.pull_unified: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaskedTrace.pull_unified"
#check @HiddenMonotonicity.MaskedTrace.pull_unified
#print axioms _ThesisExactChecks.target_4

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_5 : Prop := (∀ {n m : ℕ} (tr : MaskedTrace n m) (α : ℕ → ℝ) (seed : Sensitivity m), (tr.run α seed).1+(tr.run α seed).2=tr.bulkCoefficient α • ((seed.1+seed.2).comp tr.absMap))
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5 := by exact @HiddenMonotonicity.MaskedTrace.run_bulk
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaskedTrace.run_bulk
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaskedTrace.run_bulk"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaskedTrace.run_bulk | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.AffineReadout do
    throwError "Defining module mismatch: HiddenMonotonicity.MaskedTrace.run_bulk"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaskedTrace.run_bulk: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaskedTrace.run_bulk"
#check @HiddenMonotonicity.MaskedTrace.run_bulk
#print axioms _ThesisExactChecks.target_5

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_6 : Prop := (∀ {n m : ℕ} (tr : MaskedTrace n m) (α : ℕ → ℝ), tr.bulkCoefficient α=∏ i ∈ Finset.range (tr.depth+1), (1-2*α i))
theorem _ThesisExactChecks.target_6 : _ThesisExpectedTypes.type_6 := by exact @HiddenMonotonicity.MaskedTrace.bulkCoefficient_product
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.MaskedTrace.bulkCoefficient_product
  let expected ← getConstInfo `_ThesisExactChecks.target_6
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.MaskedTrace.bulkCoefficient_product"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.MaskedTrace.bulkCoefficient_product | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.StabilizedBackward do
    throwError "Defining module mismatch: HiddenMonotonicity.MaskedTrace.bulkCoefficient_product"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_6) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.MaskedTrace.bulkCoefficient_product: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.MaskedTrace.bulkCoefficient_product"
#check @HiddenMonotonicity.MaskedTrace.bulkCoefficient_product
#print axioms _ThesisExactChecks.target_6

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_7 := (∀ {n k : ℕ}, Matrix (Fin k) (Fin n) ℝ → Matrix (Fin k) (Fin n) ℝ → Vec k → Vec k → PairVec n → PairVec k)
noncomputable def _ThesisExactChecks.target_7 : _ThesisExpectedTypes.type_7 := by exact @HiddenMonotonicity.affineChunk
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.affineChunk
  let expected ← getConstInfo `_ThesisExactChecks.target_7
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.affineChunk"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.affineChunk | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.AffineChunk do
    throwError "Defining module mismatch: HiddenMonotonicity.affineChunk"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_7) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.affineChunk: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.affineChunk"
#check @HiddenMonotonicity.affineChunk
#print axioms _ThesisExactChecks.target_7

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_8 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (x : PairVec n), preP wp wn x+bp-(preN wp wn x+bn)=affineLayer wp wn bp bn (x.1-x.2))
theorem _ThesisExactChecks.target_8 : _ThesisExpectedTypes.type_8 := by exact @HiddenMonotonicity.preactivation_difference
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.preactivation_difference
  let expected ← getConstInfo `_ThesisExactChecks.target_8
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.preactivation_difference"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.preactivation_difference | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.OriginalTrace do
    throwError "Defining module mismatch: HiddenMonotonicity.preactivation_difference"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_8) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.preactivation_difference: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.preactivation_difference"
#check @HiddenMonotonicity.preactivation_difference
#print axioms _ThesisExactChecks.target_8

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_9 := (ℝ → (ℝ × ℝ) → ℝ × ℝ)
noncomputable def _ThesisExactChecks.target_9 : _ThesisExpectedTypes.type_9 := by exact @HiddenMonotonicity.mixPair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.mixPair
  let expected ← getConstInfo `_ThesisExactChecks.target_9
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.mixPair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.mixPair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Decomposition do
    throwError "Defining module mismatch: HiddenMonotonicity.mixPair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_9) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.mixPair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.mixPair"
#check @HiddenMonotonicity.mixPair
#print axioms _ThesisExactChecks.target_9

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_10 : Prop := (∀ p n : ℝ, max p n-n=relu (p-n))
theorem _ThesisExactChecks.target_10 : _ThesisExpectedTypes.type_10 := by exact @HiddenMonotonicity.max_sub
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.max_sub
  let expected ← getConstInfo `_ThesisExactChecks.target_10
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.max_sub"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.max_sub | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Core do
    throwError "Defining module mismatch: HiddenMonotonicity.max_sub"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_10) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.max_sub: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.max_sub"
#check @HiddenMonotonicity.max_sub
#print axioms _ThesisExactChecks.target_10

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_11 := (∀ {n k : ℕ}, Matrix (Fin k) (Fin n) ℝ → Matrix (Fin k) (Fin n) ℝ → Vec k → Vec k → PairVec n → PairVec k)
noncomputable def _ThesisExactChecks.target_11 : _ThesisExpectedTypes.type_11 := by exact @HiddenMonotonicity.layerFun
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.layerFun
  let expected ← getConstInfo `_ThesisExactChecks.target_11
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.layerFun"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.layerFun | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.NetworkDerivative do
    throwError "Defining module mismatch: HiddenMonotonicity.layerFun"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_11) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.layerFun: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.layerFun"
#check @HiddenMonotonicity.layerFun
#print axioms _ThesisExactChecks.target_11

section
universe u
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_12 := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] [DecidableEq ι], ((ι → ℝ) × (ι → ℝ)) → ℝ × ℝ)
noncomputable def _ThesisExactChecks.target_12 : _ThesisExpectedTypes.type_12.{u} := by exact @HiddenMonotonicity.finitePool.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.finitePool
  let expected ← getConstInfo `_ThesisExactChecks.target_12
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.finitePool"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.finitePool | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MaxPool do
    throwError "Defining module mismatch: HiddenMonotonicity.finitePool"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_12) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.finitePool: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.finitePool"
#check @HiddenMonotonicity.finitePool
#print axioms _ThesisExactChecks.target_12

section
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_13 : Prop := (∀ p q r s : ℝ, (p*r+q*s)-(p*s+q*r)=(p-q)*(r-s))
theorem _ThesisExactChecks.target_13 : _ThesisExpectedTypes.type_13 := by exact @HiddenMonotonicity.multiplicative_split_correct
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.multiplicative_split_correct
  let expected ← getConstInfo `_ThesisExactChecks.target_13
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.multiplicative_split_correct"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.multiplicative_split_correct | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.Chunks do
    throwError "Defining module mismatch: HiddenMonotonicity.multiplicative_split_correct"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_13) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.multiplicative_split_correct: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.multiplicative_split_correct"
#check @HiddenMonotonicity.multiplicative_split_correct
#print axioms _ThesisExactChecks.target_13

section
open HiddenMonotonicity Thesis.StoppingDecomposition
open scoped BigOperators
def _ThesisExpectedTypes.type_14 := ((ℝ × ℝ) → ℝ × ℝ)
noncomputable def _ThesisExactChecks.target_14 : _ThesisExpectedTypes.type_14 := by exact @Thesis.StoppingDecomposition.stopPair
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDecomposition.stopPair
  let expected ← getConstInfo `_ThesisExactChecks.target_14
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDecomposition.stopPair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDecomposition.stopPair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDecomposition do
    throwError "Defining module mismatch: Thesis.StoppingDecomposition.stopPair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_14) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDecomposition.stopPair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDecomposition.stopPair"
#check @Thesis.StoppingDecomposition.stopPair
#print axioms _ThesisExactChecks.target_14

section
open HiddenMonotonicity Thesis.StoppingDecomposition
open scoped BigOperators
def _ThesisExpectedTypes.type_15 := (∀ {n k : ℕ}, Matrix (Fin k) (Fin n) ℝ → Matrix (Fin k) (Fin n) ℝ → Vec k → Vec k → PairVec n → PairVec k)
noncomputable def _ThesisExactChecks.target_15 : _ThesisExpectedTypes.type_15 := by exact @Thesis.StoppingDecomposition.stopLayer
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDecomposition.stopLayer
  let expected ← getConstInfo `_ThesisExactChecks.target_15
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDecomposition.stopLayer"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDecomposition.stopLayer | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDecomposition do
    throwError "Defining module mismatch: Thesis.StoppingDecomposition.stopLayer"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_15) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDecomposition.stopLayer: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDecomposition.stopLayer"
#check @Thesis.StoppingDecomposition.stopLayer
#print axioms _ThesisExactChecks.target_15

section
open HiddenMonotonicity Thesis.GeneralRegularization
open scoped BigOperators
def _ThesisExpectedTypes.type_16 := (Regularizer → (ℝ → ℝ) → (ℝ × ℝ) → ℝ × ℝ)
noncomputable def _ThesisExactChecks.target_16 : _ThesisExpectedTypes.type_16 := by exact @Thesis.GeneralRegularization.pairWith
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.pairWith
  let expected ← getConstInfo `_ThesisExactChecks.target_16
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.pairWith"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.pairWith | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.pairWith"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_16) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.pairWith: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.pairWith"
#check @Thesis.GeneralRegularization.pairWith
#print axioms _ThesisExactChecks.target_16

section
open HiddenMonotonicity Thesis.GeneralRegularization
open scoped BigOperators
def _ThesisExpectedTypes.type_17 := (∀ θ : ℝ, 0<θ → Regularizer)
noncomputable def _ThesisExactChecks.target_17 : _ThesisExpectedTypes.type_17 := by exact @Thesis.GeneralRegularization.entropyRegularizer
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.entropyRegularizer
  let expected ← getConstInfo `_ThesisExactChecks.target_17
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.entropyRegularizer"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.entropyRegularizer | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.entropyRegularizer"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_17) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.entropyRegularizer: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.entropyRegularizer"
#check @Thesis.GeneralRegularization.entropyRegularizer
#print axioms _ThesisExactChecks.target_17

section
open HiddenMonotonicity Thesis.GeneralRegularization
open scoped BigOperators
def _ThesisExpectedTypes.type_18 : Prop := (∀ z : ℝ, hardGate z ∈ Set.Icc (0 : ℝ) 1 ∧ IsMaxOn (objective zeroRegularizer z) (Set.Icc 0 1) (hardGate z))
theorem _ThesisExactChecks.target_18 : _ThesisExpectedTypes.type_18 := by exact @Thesis.GeneralRegularization.hardGate_optimal
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.hardGate_optimal
  let expected ← getConstInfo `_ThesisExactChecks.target_18
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.hardGate_optimal"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.hardGate_optimal | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.hardGate_optimal"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_18) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.hardGate_optimal: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.hardGate_optimal"
#check @Thesis.GeneralRegularization.hardGate_optimal
#print axioms _ThesisExactChecks.target_18

section
open HiddenMonotonicity Thesis.Regularization
open scoped BigOperators
def _ThesisExpectedTypes.type_19 := (ℝ → ℝ → ℝ → ℝ × ℝ)
noncomputable def _ThesisExactChecks.target_19 : _ThesisExpectedTypes.type_19 := by exact @Thesis.Regularization.softSplit
end
run_cmd do
  let target ← getConstInfo `Thesis.Regularization.softSplit
  let expected ← getConstInfo `_ThesisExactChecks.target_19
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Regularization.softSplit"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Regularization.softSplit | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Regularization do
    throwError "Defining module mismatch: Thesis.Regularization.softSplit"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_19) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Regularization.softSplit: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Regularization.softSplit"
#check @Thesis.Regularization.softSplit
#print axioms _ThesisExactChecks.target_19

section
open HiddenMonotonicity Thesis.Regularization
open scoped BigOperators
def _ThesisExpectedTypes.type_20 : Prop := (∀ (θ z : ℝ) (hθ : 0<θ), gate θ z*z+θ*Real.binEntropy (gate θ z)=softplus θ z)
theorem _ThesisExactChecks.target_20 : _ThesisExpectedTypes.type_20 := by exact @Thesis.Regularization.entropy_gate_value
end
run_cmd do
  let target ← getConstInfo `Thesis.Regularization.entropy_gate_value
  let expected ← getConstInfo `_ThesisExactChecks.target_20
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Regularization.entropy_gate_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Regularization.entropy_gate_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Regularization do
    throwError "Defining module mismatch: Thesis.Regularization.entropy_gate_value"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_20) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Regularization.entropy_gate_value: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Regularization.entropy_gate_value"
#check @Thesis.Regularization.entropy_gate_value
#print axioms _ThesisExactChecks.target_20

section
universe u
open HiddenMonotonicity Thesis.ReferencePolicy
open scoped BigOperators
def _ThesisExpectedTypes.type_21 : Prop := (∀ {A : Type u} [Fintype A] (ρ u : A → ℝ) (hu : ∀ i,0<u i), referencePolicy 1 ρ (fun i => Real.log (u i))=(fun i => ρ i*u i/∑ j,ρ j*u j))
theorem _ThesisExactChecks.target_21 : _ThesisExpectedTypes.type_21.{u} := by exact @Thesis.ReferencePolicy.reference_log_policy.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.ReferencePolicy.reference_log_policy
  let expected ← getConstInfo `_ThesisExactChecks.target_21
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.ReferencePolicy.reference_log_policy"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReferencePolicy.reference_log_policy | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReferencePolicy do
    throwError "Defining module mismatch: Thesis.ReferencePolicy.reference_log_policy"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_21) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ReferencePolicy.reference_log_policy: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReferencePolicy.reference_log_policy"
#check @Thesis.ReferencePolicy.reference_log_policy
#print axioms _ThesisExactChecks.target_21

section
universe u
open HiddenMonotonicity Thesis.ReferencePolicy
open scoped BigOperators
def _ThesisExpectedTypes.type_22 : Prop := (∀ {A : Type u} [Fintype A] [Nonempty A] (θ : ℝ) (ρ q : A → ℝ) (hθ : 0<θ) (hρ : ∀ i,0<ρ i), (∑ i,referencePolicy θ ρ q i*q i)-θ*kl (referencePolicy θ ρ q) ρ=referenceValue θ ρ q)
theorem _ThesisExactChecks.target_22 : _ThesisExpectedTypes.type_22.{u} := by exact @Thesis.ReferencePolicy.reference_policy_value.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.ReferencePolicy.reference_policy_value
  let expected ← getConstInfo `_ThesisExactChecks.target_22
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.ReferencePolicy.reference_policy_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReferencePolicy.reference_policy_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReferencePolicy do
    throwError "Defining module mismatch: Thesis.ReferencePolicy.reference_policy_value"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_22) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ReferencePolicy.reference_policy_value: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReferencePolicy.reference_policy_value"
#check @Thesis.ReferencePolicy.reference_policy_value
#print axioms _ThesisExactChecks.target_22

section
universe u v
open HiddenMonotonicity Thesis.Games
open scoped BigOperators
def _ThesisExpectedTypes.type_23 : Prop := (∀ {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] [DecidableEq Y] (p q : X → ℝ) (terminal : X → Y) (y : Y), pixelDisagreement p q terminal y=((∑ x,if terminal x=y then p x else 0)+(∑ x,if terminal x=y then q x else 0))/2-∑ x,if terminal x=y then Real.sqrt (p x*q x) else 0)
theorem _ThesisExactChecks.target_23 : _ThesisExpectedTypes.type_23.{u, v} := by exact @Thesis.Games.pixelDisagreement_formula.{u, v}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.pixelDisagreement_formula
  let expected ← getConstInfo `_ThesisExactChecks.target_23
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: Thesis.Games.pixelDisagreement_formula"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.pixelDisagreement_formula | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.pixelDisagreement_formula"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_23) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.pixelDisagreement_formula: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.pixelDisagreement_formula"
#check @Thesis.Games.pixelDisagreement_formula
#print axioms _ThesisExactChecks.target_23

section
universe u v
open HiddenMonotonicity Thesis.Games
open scoped BigOperators
def _ThesisExpectedTypes.type_24 : Prop := (∀ {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] [DecidableEq Y] (p q : X → ℝ) (terminal : X → Y) (hp1 : ∑ x,p x=1) (hq1 : ∑ x,q x=1), (∑ y,pixelDisagreement p q terminal y)=1-overlap p q)
theorem _ThesisExactChecks.target_24 : _ThesisExpectedTypes.type_24.{u, v} := by exact @Thesis.Games.pixelDisagreement_total.{u, v}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.pixelDisagreement_total
  let expected ← getConstInfo `_ThesisExactChecks.target_24
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: Thesis.Games.pixelDisagreement_total"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.pixelDisagreement_total | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.pixelDisagreement_total"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_24) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.pixelDisagreement_total: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.pixelDisagreement_total"
#check @Thesis.Games.pixelDisagreement_total
#print axioms _ThesisExactChecks.target_24

section
universe u
open HiddenMonotonicity Thesis.Games
open scoped BigOperators
def _ThesisExpectedTypes.type_25 : Prop := (∀ {S : Type u} [Fintype S] (p q : S → ℝ) (hp : ∀ s,0≤p s) (hq : ∀ s,0≤q s) (hp1 : ∑ s,p s=1) (hq1 : ∑ s,q s=1), overlap p q≤1)
theorem _ThesisExactChecks.target_25 : _ThesisExpectedTypes.type_25.{u} := by exact @Thesis.Games.overlap_le_one.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.overlap_le_one
  let expected ← getConstInfo `_ThesisExactChecks.target_25
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Games.overlap_le_one"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.overlap_le_one | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.overlap_le_one"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_25) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.overlap_le_one: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.overlap_le_one"
#check @Thesis.Games.overlap_le_one
#print axioms _ThesisExactChecks.target_25

section
universe u
open HiddenMonotonicity Thesis.Games
open scoped BigOperators
def _ThesisExpectedTypes.type_26 : Prop := (∀ {S : Type u} [Fintype S] (p q : S → ℝ), 0≤overlap p q)
theorem _ThesisExactChecks.target_26 : _ThesisExpectedTypes.type_26.{u} := by exact @Thesis.Games.overlap_nonneg.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.overlap_nonneg
  let expected ← getConstInfo `_ThesisExactChecks.target_26
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Games.overlap_nonneg"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.overlap_nonneg | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.overlap_nonneg"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_26) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.overlap_nonneg: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.overlap_nonneg"
#check @Thesis.Games.overlap_nonneg
#print axioms _ThesisExactChecks.target_26

section
open HiddenMonotonicity Thesis.RoutingSupport
open scoped BigOperators
def _ThesisExpectedTypes.type_27 := (∀ {n k : ℕ}, Matrix (Fin k) (Fin n) ℝ → Matrix (Fin k) (Fin n) ℝ → Vec k → Vec k → ℝ → ℝ → ℝ → Vec n → Matrix (Fin k) (Fin n) ℝ)
noncomputable def _ThesisExactChecks.target_27 : _ThesisExpectedTypes.type_27 := by exact @Thesis.RoutingSupport.sourceLayer
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingSupport.sourceLayer
  let expected ← getConstInfo `_ThesisExactChecks.target_27
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingSupport.sourceLayer"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingSupport.sourceLayer | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingSupport do
    throwError "Defining module mismatch: Thesis.RoutingSupport.sourceLayer"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_27) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingSupport.sourceLayer: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingSupport.sourceLayer"
#check @Thesis.RoutingSupport.sourceLayer
#print axioms _ThesisExactChecks.target_27

section
open HiddenMonotonicity Thesis.RoutingSupport
open scoped BigOperators
def _ThesisExpectedTypes.type_28 := (∀ {n m : ℕ}, ℝ → ℝ → ℝ → Network n m → Vec n → Vec m → Vec n)
noncomputable def _ThesisExactChecks.target_28 : _ThesisExpectedTypes.type_28 := by exact @Thesis.RoutingSupport.sourceLRP
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingSupport.sourceLRP
  let expected ← getConstInfo `_ThesisExactChecks.target_28
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingSupport.sourceLRP"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingSupport.sourceLRP | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingSupport do
    throwError "Defining module mismatch: Thesis.RoutingSupport.sourceLRP"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_28) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingSupport.sourceLRP: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingSupport.sourceLRP"
#check @Thesis.RoutingSupport.sourceLRP
#print axioms _ThesisExactChecks.target_28

section
open HiddenMonotonicity Thesis.Games
open scoped BigOperators
def _ThesisExpectedTypes.type_29 := (∀ {S : Type}, (n : ℕ) → (ℕ → S → S → ℝ) → S → Paths S n → ℝ)
noncomputable def _ThesisExactChecks.target_29 : _ThesisExpectedTypes.type_29 := by exact @Thesis.Games.pathLaw
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.pathLaw
  let expected ← getConstInfo `_ThesisExactChecks.target_29
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Games.pathLaw"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.pathLaw | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.pathLaw"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_29) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.pathLaw: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.pathLaw"
#check @Thesis.Games.pathLaw
#print axioms _ThesisExactChecks.target_29

section
open HiddenMonotonicity Thesis.Games
open scoped BigOperators
def _ThesisExpectedTypes.type_30 := (∀ {S : Type} [Fintype S], ℕ → (ℕ → S → S → ℝ) → (S → ℝ) → S → ℝ)
noncomputable def _ThesisExactChecks.target_30 : _ThesisExpectedTypes.type_30 := by exact @Thesis.Games.backwardDP
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.backwardDP
  let expected ← getConstInfo `_ThesisExactChecks.target_30
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Games.backwardDP"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.backwardDP | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.backwardDP"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_30) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.backwardDP: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.backwardDP"
#check @Thesis.Games.backwardDP
#print axioms _ThesisExactChecks.target_30

section
universe u
open HiddenMonotonicity Thesis.Games
open scoped BigOperators
def _ThesisExpectedTypes.type_31 := (∀ {S : Type u} [Fintype S], (S → ℝ) → (S → ℝ) → ℝ)
noncomputable def _ThesisExactChecks.target_31 : _ThesisExpectedTypes.type_31.{u} := by exact @Thesis.Games.overlap.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.overlap
  let expected ← getConstInfo `_ThesisExactChecks.target_31
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Games.overlap"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.overlap | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.overlap"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_31) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Games.overlap: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.overlap"
#check @Thesis.Games.overlap
#print axioms _ThesisExactChecks.target_31

section
open HiddenMonotonicity Thesis.Tropical
open scoped BigOperators
def _ThesisExpectedTypes.type_32 := (∀ {I : Type} [Fintype I], Polynomial I → (I → ℝ) → ℝ)
noncomputable def _ThesisExactChecks.target_32 : _ThesisExpectedTypes.type_32 := by exact @Thesis.Tropical.Polynomial.eval
end
run_cmd do
  let target ← getConstInfo `Thesis.Tropical.Polynomial.eval
  let expected ← getConstInfo `_ThesisExactChecks.target_32
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Tropical.Polynomial.eval"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Tropical.Polynomial.eval | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Tropical do
    throwError "Defining module mismatch: Thesis.Tropical.Polynomial.eval"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_32) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Tropical.Polynomial.eval: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Tropical.Polynomial.eval"
#check @Thesis.Tropical.Polynomial.eval
#print axioms _ThesisExactChecks.target_32

section
open HiddenMonotonicity Thesis.Tropical
open scoped BigOperators
def _ThesisExpectedTypes.type_33 := (∀ {I : Type}, Polynomial I → Set (I → ℝ))
noncomputable def _ThesisExactChecks.target_33 : _ThesisExpectedTypes.type_33 := by exact @Thesis.Tropical.Polynomial.newton
end
run_cmd do
  let target ← getConstInfo `Thesis.Tropical.Polynomial.newton
  let expected ← getConstInfo `_ThesisExactChecks.target_33
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Tropical.Polynomial.newton"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Tropical.Polynomial.newton | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Tropical do
    throwError "Defining module mismatch: Thesis.Tropical.Polynomial.newton"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_33) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Tropical.Polynomial.newton: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Tropical.Polynomial.newton"
#check @Thesis.Tropical.Polynomial.newton
#print axioms _ThesisExactChecks.target_33

section
open HiddenMonotonicity Thesis.Tropical
open scoped BigOperators
def _ThesisExpectedTypes.type_34 := (∀ {I : Type} [Fintype I], Set (I → ℝ) → (I → ℝ) → ℝ)
noncomputable def _ThesisExactChecks.target_34 : _ThesisExpectedTypes.type_34 := by exact @Thesis.Tropical.support
end
run_cmd do
  let target ← getConstInfo `Thesis.Tropical.support
  let expected ← getConstInfo `_ThesisExactChecks.target_34
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Tropical.support"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Tropical.support | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Tropical do
    throwError "Defining module mismatch: Thesis.Tropical.support"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_34) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.Tropical.support: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Tropical.support"
#check @Thesis.Tropical.support
#print axioms _ThesisExactChecks.target_34

section
open HiddenMonotonicity Thesis.StoppingDAG
open scoped BigOperators
def _ThesisExpectedTypes.type_35 := (∀ {d n : ℕ} (c : Circuit d n), PairVec d → Fin n → Thesis.StoppingDAG.DAGPaths c → ℝ)
noncomputable def _ThesisExactChecks.target_35 : _ThesisExpectedTypes.type_35 := by exact @Thesis.StoppingDAG.pathProbability
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.pathProbability
  let expected ← getConstInfo `_ThesisExactChecks.target_35
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.pathProbability"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.pathProbability | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGPaths do
    throwError "Defining module mismatch: Thesis.StoppingDAG.pathProbability"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_35) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.pathProbability: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.pathProbability"
#check @Thesis.StoppingDAG.pathProbability
#print axioms _ThesisExactChecks.target_35

section
open HiddenMonotonicity Thesis.StoppingDAG
open scoped BigOperators
def _ThesisExpectedTypes.type_36 := (∀ {d n : ℕ}, Circuit d n → PairVec d → Fin n → Bool → ℕ → Bool → ℝ)
noncomputable def _ThesisExactChecks.target_36 : _ThesisExpectedTypes.type_36 := by exact @Thesis.StoppingDAG.fullOccupation
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDAG.fullOccupation
  let expected ← getConstInfo `_ThesisExactChecks.target_36
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDAG.fullOccupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDAG.fullOccupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDAGVisits do
    throwError "Defining module mismatch: Thesis.StoppingDAG.fullOccupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_36) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.StoppingDAG.fullOccupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDAG.fullOccupation"
#check @Thesis.StoppingDAG.fullOccupation
#print axioms _ThesisExactChecks.target_36

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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/dc_decompose/master_thesis/reports/evidence/lean-link-review/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

