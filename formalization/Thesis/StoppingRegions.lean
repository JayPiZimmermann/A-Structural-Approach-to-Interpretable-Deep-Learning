import Thesis.StoppingBoundary
import HiddenMonotonicity.DifferentiableHeads

noncomputable section
namespace Thesis.StoppingStructure
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.BackwardGames

/-- Equality of every original forward gate, stated recursively on actual inputs. -/
def SameGates {n m} : Network n m → Vec n → Vec n → Prop
  | .output _, _, _ => True
  | .layer wp wn bp bn tail, x, y =>
      originalGate wp wn bp bn x = originalGate wp wn bp bn y ∧
      SameGates tail (reluLayer wp wn bp bn x) (reluLayer wp wn bp bn y)

theorem sameGates_refl {n m} (net : Network n m) (x : Vec n) : SameGates net x x := by
  induction net with
  | output n => trivial
  | layer wp wn bp bn tail ih => exact ⟨rfl,ih _⟩

/-- Region is defined by actual original gate values, not by a monotonicity premise. -/
def gateRegion {n m} (net : Network n m) (reference : Vec n) : Set (PairVec n) :=
  {x | SameGates net (x.1-x.2) reference}

def gatedBias {k} (g : Fin k → Bool) (bp bn : Vec k) : PairVec k :=
  (MaskedTrace.activeMap g bp,MaskedTrace.activeMap g bn)

/-- Affine extension obtained by freezing only the original gate pattern. -/
def frozenStopping {n m} : Network n m → Vec n → PairVec n → PairVec m
  | .output _, _, x => x
  | .layer wp wn bp bn tail, r, x =>
      frozenStopping tail (reluLayer wp wn bp bn r)
        (stopLayerJac wp wn (originalGate wp wn bp bn r) x +
          gatedBias (originalGate wp wn bp bn r) bp bn)

theorem stopLayer_frozen {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) :
    stopLayer wp wn bp bn x =
      stopLayerJac wp wn (originalGate wp wn bp bn (x.1-x.2)) x +
        gatedBias (originalGate wp wn bp bn (x.1-x.2)) bp bn := by
  rw [← layerGate_original]
  apply Prod.ext <;> funext i
  all_goals
    simp only [stopLayer, stopPair, stopLayerJac, gatedBias, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, MaskedTrace.activeMap_apply, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, decide_eq_true_eq]
    split_ifs <;> simp

theorem stopping_eq_frozen {n m} (net : Network n m) (r : Vec n) (x : PairVec n)
    (hx : SameGates net (x.1-x.2) r) : net.decomposeWith stopPair x = frozenStopping net r x := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      change tail.decomposeWith stopPair (stopLayer wp wn bp bn x) = _
      have ht : SameGates tail ((stopLayer wp wn bp bn x).1-(stopLayer wp wn bp bn x).2)
          (reluLayer wp wn bp bn r) := by
        rw [stopLayer_difference]
        exact hx.2
      rw [ih _ _ ht, stopLayer_frozen, hx.1]
      rfl

/-- The affine extension has the actual fixed-gate stopping Jacobian as its
linear part, including arbitrary layer biases. -/
theorem frozenStopping_affine {n m} (net : Network n m) (r : Vec n) (x : PairVec n) :
    frozenStopping net r x = stoppingJac (net.originalTrace r) x + frozenStopping net r 0 := by
  induction net with
  | output n => simp [frozenStopping, stoppingJac, Network.originalTrace]
  | layer wp wn bp bn tail ih =>
      simp only [frozenStopping, Network.originalTrace, stoppingJac, ContinuousLinearMap.comp_apply]
      conv_lhs => rw [ih]
      conv_rhs => rw [ih]
      simp only [map_add, map_zero, zero_add]
      abel

theorem activeMap_monotone {n} (g : Fin n → Bool) : Monotone (MaskedTrace.activeMap g) := by
  intro x y h i
  simp only [MaskedTrace.activeMap_apply]
  cases g i <;> simp [h i]

theorem stoppingJac_monotone {n m} (tr : MaskedTrace n m) (hw : NonnegativeWeights tr) :
    Monotone (stoppingJac tr) := by
  induction tr with
  | output n => exact monotone_id
  | layer wp wn g tail ih =>
      apply (ih hw.2).comp
      intro x y h
      exact ⟨activeMap_monotone g (preP_monotone wp wn hw.1 h),
        activeMap_monotone g (preP_monotone wn wp (fun i j => ⟨(hw.1 i j).2,(hw.1 i j).1⟩) h)⟩

theorem trace_nonnegative {n m} (net : Network n m) (hw : net.Nonnegative) (r : Vec n) :
    NonnegativeWeights (net.originalTrace r) := by
  induction net with
  | output n => trivial
  | layer wp wn bp bn tail ih => exact ⟨fun i j => ⟨hw.1 i j,hw.2.1 i j⟩,ih hw.2.2 _⟩

/-- Source lem:stop_monotone: actual stopping streams are affine with a monotone
linear part and coordinatewise monotone on every fixed original-gate region. -/
theorem stopping_region_affine_monotone {n m} (net : Network n m) (hw : net.Nonnegative)
    (r : Vec n) :
    Monotone (stoppingJac (net.originalTrace r)) ∧
    (∀ x ∈ gateRegion net r, net.decomposeWith stopPair x =
      stoppingJac (net.originalTrace r) x + frozenStopping net r 0) ∧
    MonotoneOn (net.decomposeWith stopPair) (gateRegion net r) := by
  have hm := stoppingJac_monotone (net.originalTrace r) (trace_nonnegative net hw r)
  refine ⟨hm, ?_, ?_⟩
  · intro x hx
    rw [stopping_eq_frozen net r x hx, frozenStopping_affine]
  · intro x hx y hy hxy
    rw [stopping_eq_frozen net r x hx, stopping_eq_frozen net r y hy,
      frozenStopping_affine net r x, frozenStopping_affine net r y]
    exact ⟨add_le_add (hm hxy).1 le_rfl,add_le_add (hm hxy).2 le_rfl⟩

/-- Vanishing biases are an explicit network hypothesis for the input-only path formula. -/
def ZeroBias {n m} : Network n m → Prop
  | .output _ => True
  | .layer _ _ bp bn tail => bp=0 ∧ bn=0 ∧ ZeroBias tail

theorem frozenStopping_zero {n m} (net : Network n m) (hb : ZeroBias net) (r : Vec n) :
    frozenStopping net r 0 = 0 := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [frozenStopping, hb.1, hb.2.1, gatedBias, map_zero, Prod.mk_zero_zero, add_zero]
      exact ih hb.2.2 _

theorem stopping_zeroBias_linear {n m} (net : Network n m) (hb : ZeroBias net) (x : PairVec n) :
    net.decomposeWith stopPair x = stoppingJac (net.originalTrace (x.1-x.2)) x := by
  rw [stopping_eq_frozen net (x.1-x.2) x (sameGates_refl net _),
    frozenStopping_affine, frozenStopping_zero net hb, add_zero]

/-- One term for each bias stub, propagated through all later frozen gates. -/
def biasSources {n m} : Network n m → Vec n → List (PairVec m)
  | .output _, _ => []
  | .layer wp wn bp bn tail, r =>
      stoppingJac (tail.originalTrace (reluLayer wp wn bp bn r))
        (gatedBias (originalGate wp wn bp bn r) bp bn) ::
      biasSources tail (reluLayer wp wn bp bn r)

theorem frozenStopping_zero_biasSources {n m} (net : Network n m) (r : Vec n) :
    frozenStopping net r 0 = (biasSources net r).sum := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [frozenStopping, map_zero, zero_add, biasSources, List.sum_cons]
      rw [frozenStopping_affine, ih]

/-- Exact bias-stub extension of the input-only homogeneous path formula. -/
theorem stopping_input_and_bias_sources {n m} (net : Network n m) (x : PairVec n) :
    net.decomposeWith stopPair x = stoppingJac (net.originalTrace (x.1-x.2)) x +
      (biasSources net (x.1-x.2)).sum := by
  rw [stopping_eq_frozen net _ x (sameGates_refl net _), frozenStopping_affine,
    frozenStopping_zero_biasSources]

theorem parameters_nonnegative_weights {n m} (net : Network n m) (hp : net.NonnegativeParameters) :
    net.Nonnegative := by
  induction net with
  | output n => trivial
  | layer wp wn bp bn tail ih => exact ⟨fun i j => (hp.1 i j).1,fun i j => (hp.1 i j).2,ih hp.2.2⟩

theorem frozenStopping_nonnegative {n m} (net : Network n m) (hp : net.NonnegativeParameters)
    (r : Vec n) (x : PairVec n) (hx : 0≤x) : 0≤frozenStopping net r x := by
  induction net with
  | output n => exact hx
  | layer wp wn bp bn tail ih =>
      apply ih hp.2.2
      have hlin := stoppingJac_monotone
        (MaskedTrace.layer wp wn (originalGate wp wn bp bn r) (.output _)) ⟨hp.1,trivial⟩ hx
      have hlin' : 0≤stopLayerJac wp wn (originalGate wp wn bp bn r) x := by
        simpa only [stoppingJac,ContinuousLinearMap.id_comp,map_zero] using hlin
      have hb : 0≤gatedBias (originalGate wp wn bp bn r) bp bn := by
        constructor <;> intro i
        · simp only [gatedBias,MaskedTrace.activeMap_apply]
          split_ifs
          · exact (hp.2.1 i).1
          · exact le_rfl
        · simp only [gatedBias,MaskedTrace.activeMap_apply]
          split_ifs
          · exact (hp.2.1 i).2
          · exact le_rfl
      exact ⟨add_nonneg hlin'.1 hb.1,add_nonneg hlin'.2 hb.2⟩


/-- Complete nonnegative-affine region statement, including its bias constant. -/
theorem stopping_region_nonnegative_affine {n m} (net : Network n m)
    (hp : net.NonnegativeParameters) (r : Vec n) :
    0≤frozenStopping net r 0 ∧ Monotone (stoppingJac (net.originalTrace r)) ∧
    (∀ x ∈ gateRegion net r, net.decomposeWith stopPair x =
      stoppingJac (net.originalTrace r) x + frozenStopping net r 0) ∧
    MonotoneOn (net.decomposeWith stopPair) (gateRegion net r) :=
  ⟨frozenStopping_nonnegative net hp r 0 le_rfl,
    stopping_region_affine_monotone net (parameters_nonnegative_weights net hp) r⟩

end Thesis.StoppingStructure
