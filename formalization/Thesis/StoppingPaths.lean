import Thesis.StoppingRegions

noncomputable section
namespace Thesis.StoppingStructure
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.BackwardGames Matrix
open scoped BigOperators

/-- Ordinary neuron-index paths, without artificially independent sign choices. -/
def GeometricPaths {n m} : MaskedTrace n m → Type
  | .output _ => Unit
  | @MaskedTrace.layer _ k _ _ _ _ tail => Fin k × GeometricPaths tail

instance geometricPathsFintype {n m} : (tr : MaskedTrace n m) → Fintype (GeometricPaths tr)
  | .output _ => inferInstanceAs (Fintype Unit)
  | .layer _ _ _ tail => @instFintypeProd _ _ _ (geometricPathsFintype tail)

/-- XOR is parity of the actual negative signed weights along the neuron path. -/
def geometricParity {n m} : (tr : MaskedTrace n m) → Fin n → GeometricPaths tr → Bool
  | .output _, _, _ => false
  | .layer wp wn _ tail, i, path =>
      Bool.xor (decide (wp path.1 i-wn path.1 i<0)) (geometricParity tail path.1 path.2)

/-- Literal count of negative weights on the same ordinary neuron path. -/
def negativeEdgeCount {n m} : (tr : MaskedTrace n m) → Fin n → GeometricPaths tr → ℕ
  | .output _, _, _ => 0
  | .layer wp wn _ tail, i, path =>
      negativeEdgeCount tail path.1 path.2 + (if wp path.1 i-wn path.1 i<0 then 1 else 0)

theorem geometricParity_negative_count {n m} (tr : MaskedTrace n m) (i : Fin n)
    (path : GeometricPaths tr) :
    geometricParity tr i path = decide (Odd (negativeEdgeCount tr i path)) := by
  induction tr with
  | output n => simp [geometricParity,negativeEdgeCount]
  | layer wp wn g tail ih =>
      simp only [geometricParity,negativeEdgeCount,ih]
      by_cases h : wp path.1 i-wn path.1 i<0
      · by_cases ho : Odd (negativeEdgeCount tail path.1 path.2)
        · have he := Nat.not_even_iff_odd.mpr ho
          simp [h,Nat.odd_add_one,ho,he]
        · have he := Nat.not_odd_iff_even.mp ho
          simp [h,Nat.odd_add_one,ho,he]
      · simp [h]

/-- Product of absolute signed weights and traversed gates. The terminal Kronecker
factor enforces the specified output endpoint. Zero edges contribute zero. -/
def geometricWeight {n m} : (tr : MaskedTrace n m) → Fin m → Fin n → GeometricPaths tr → ℝ
  | .output _, j, i, _ => if j=i then 1 else 0
  | .layer wp wn g tail, j, i, path =>
      (if g path.1 then |wp path.1 i-wn path.1 i| else 0) * geometricWeight tail j path.1 path.2

def geometricKernel {n m} (tr : MaskedTrace n m) (j : Fin m) (i : Fin n)
    (parity : Bool) (path : GeometricPaths tr) : ℝ :=
  if geometricParity tr i path=parity then geometricWeight tr j i path else 0

def CanonicalTrace {n m} : MaskedTrace n m → Prop
  | .output _ => True
  | .layer wp wn _ tail =>
      (∀ j i, wp j i=max (wp j i-wn j i) 0 ∧ wn j i=max (-(wp j i-wn j i)) 0) ∧ CanonicalTrace tail

theorem trace_canonical {n m} (net : Network n m) (hc : net.Canonical) (r : Vec n) :
    CanonicalTrace (net.originalTrace r) := by
  induction net with
  | output n => trivial
  | layer wp wn bp bn tail ih => exact ⟨hc.1,ih hc.2 _⟩

theorem canonical_edge_parity (w v : ℝ) (g p q : Bool) :
    (if Bool.xor (decide (w<0)) q = p then (if g then |w| else 0)*v else 0) =
      (if g then max w 0 else 0)*(if q=p then v else 0) +
      (if g then max (-w) 0 else 0)*(if q= !p then v else 0) := by
  by_cases h : w<0
  · have hn : 0≤-w := by linarith
    cases g <;> cases p <;> cases q <;>
      simp [h,abs_of_neg h,max_eq_right h.le,max_eq_left hn]
  · have hp : 0≤w := le_of_not_gt h
    have hn : -w≤0 := neg_nonpos.mpr hp
    cases g <;> cases p <;> cases q <;>
      simp [h,abs_of_nonneg hp,max_eq_left hp,max_eq_right hn]

theorem geometricKernel_layer {n k m} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (g : Fin k → Bool) (tail : MaskedTrace k m)
    (hc : ∀ j i, wp j i=max (wp j i-wn j i) 0 ∧ wn j i=max (-(wp j i-wn j i)) 0)
    (j : Fin m) (i : Fin n) (p : Bool) (path : GeometricPaths (.layer wp wn g tail)) :
    geometricKernel (.layer wp wn g tail) j i p path =
      gated g wp path.1 i * geometricKernel tail j path.1 p path.2 +
      gated g wn path.1 i * geometricKernel tail j path.1 (!p) path.2 := by
  have h := canonical_edge_parity (wp path.1 i-wn path.1 i)
    (geometricWeight tail j path.1 path.2) (g path.1) p (geometricParity tail path.1 path.2)
  rw [← (hc path.1 i).1,← (hc path.1 i).2] at h
  exact h

/-- Geometric parity sums are exactly the established occupation parity kernels. -/
theorem geometric_path_integral {n m} (tr : MaskedTrace n m) (hc : CanonicalTrace tr)
    (j : Fin m) (i : Fin n) :
    (∑ path : GeometricPaths tr, geometricKernel tr j i false path) = (occupations tr).1 j i ∧
    (∑ path : GeometricPaths tr, geometricKernel tr j i true path) = (occupations tr).2 j i := by
  induction tr with
  | output n =>
      change (∑ _ : Unit, (if j=i then (1 : ℝ) else 0)) = _ ∧ (∑ _ : Unit, (0 : ℝ)) = _
      simp [occupations,Matrix.one_apply]
  | @layer n k m wp wn g tail ih =>
      have ihp (h : Fin k) := (ih hc.2 j h).1
      have ihn (h : Fin k) := (ih hc.2 j h).2
      constructor
      all_goals
        simp_rw [geometricKernel_layer wp wn g tail hc.1]
        simp only [GeometricPaths,Fintype.sum_prod_type]
        simp only [Bool.not_false,Bool.not_true,Finset.sum_add_distrib,← Finset.mul_sum]
        simp_rw [ihp,ihn]
        simp only [occupations,Matrix.add_apply,Matrix.mul_apply,Finset.sum_add_distrib,mul_comm,add_comm]

theorem geometric_input_sum {n m} (tr : MaskedTrace n m) (j : Fin m) (i : Fin n) (p q : ℝ) :
    (∑ path : GeometricPaths tr, geometricKernel tr j i false path)*p +
      (∑ path : GeometricPaths tr, geometricKernel tr j i true path)*q =
      ∑ path : GeometricPaths tr, geometricWeight tr j i path * (if geometricParity tr i path then q else p) := by
  rw [Finset.sum_mul,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro path _
  cases hp : geometricParity tr i path <;> simp [geometricKernel,hp]

theorem stoppingJac_geometric_paths {n m} (tr : MaskedTrace n m) (hc : CanonicalTrace tr)
    (x : PairVec n) (j : Fin m) :
    (stoppingJac tr x).1 j = ∑ i, ∑ path : GeometricPaths tr,
      geometricWeight tr j i path * (if geometricParity tr i path then x.2 i else x.1 i) ∧
    (stoppingJac tr x).2 j = ∑ i, ∑ path : GeometricPaths tr,
      geometricWeight tr j i path * (if geometricParity tr i path then x.1 i else x.2 i) := by
  rw [stoppingJac_occupation]
  constructor
  · change (∑ i, (occupations tr).1 j i*x.1 i)+(∑ i, (occupations tr).2 j i*x.2 i) = _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← (geometric_path_integral tr hc j i).1,← (geometric_path_integral tr hc j i).2]
    exact geometric_input_sum tr j i _ _
  · change (∑ i, (occupations tr).2 j i*x.1 i)+(∑ i, (occupations tr).1 j i*x.2 i) = _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [add_comm,← (geometric_path_integral tr hc j i).1,← (geometric_path_integral tr hc j i).2]
    exact geometric_input_sum tr j i _ _

/-- Actual stopping activations are sorted by parity of real negative edges. -/
theorem stopping_activation_parity_paths {n m} (net : Network n m) (hc : net.Canonical)
    (hb : ZeroBias net) (x : PairVec n) (j : Fin m) :
    let tr := net.originalTrace (x.1-x.2)
    (net.decomposeWith stopPair x).1 j = ∑ i, ∑ path : GeometricPaths tr,
      geometricWeight tr j i path * (if geometricParity tr i path then x.2 i else x.1 i) ∧
    (net.decomposeWith stopPair x).2 j = ∑ i, ∑ path : GeometricPaths tr,
      geometricWeight tr j i path * (if geometricParity tr i path then x.1 i else x.2 i) := by
  rw [stopping_zeroBias_linear net hb]
  exact stoppingJac_geometric_paths _ (trace_canonical net hc _) x j

/-- Attach a trace segment; no new network semantics are introduced. -/
def appendTrace {a b c} : MaskedTrace a b → MaskedTrace b c → MaskedTrace a c
  | .output _, t => t
  | .layer wp wn g tail, t => .layer wp wn g (appendTrace tail t)

theorem stoppingJac_appendTrace {a b c} (s : MaskedTrace a b) (t : MaskedTrace b c) :
    stoppingJac (appendTrace s t) = (stoppingJac t).comp (stoppingJac s) := by
  induction s with
  | output n => simp [appendTrace,stoppingJac]
  | layer wp wn g tail ih => simp only [appendTrace,stoppingJac,ih,ContinuousLinearMap.comp_assoc]

theorem appendTrace_canonical {a b c} (s : MaskedTrace a b) (t : MaskedTrace b c)
    (hs : CanonicalTrace s) (ht : CanonicalTrace t) : CanonicalTrace (appendTrace s t) := by
  induction s with
  | output n => exact ht
  | layer wp wn g tail ih => exact ⟨hs.1,ih t hs.2 ht⟩

def preactivationTrace {n m k} (net : Network n m) (r : Vec n)
    (wp wn : Matrix (Fin k) (Fin m) ℝ) : MaskedTrace n k :=
  appendTrace (net.originalTrace r) (.layer wp wn (fun _ => true) (.output k))

theorem ungated_stopLayerJac {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) :
    stopLayerJac wp wn (fun _ => true) = pairMap wp wn := by
  apply ContinuousLinearMap.ext
  intro x
  apply Prod.ext <;> funext i <;> simp [stopLayerJac,pairMap]

/-- Source lem:parity_path and ptnb:lem:parity-path, for actual preactivations.
The final affine edge is ungated; exactly the intermediate ReLU gates occur.
Zero weights remain in the finite index set but have zero absolute product. -/
theorem stopping_preactivation_parity_paths {n m k} (net : Network n m) (hc : net.Canonical)
    (hb : ZeroBias net) (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hw : ∀ j i, wp j i=max (wp j i-wn j i) 0 ∧ wn j i=max (-(wp j i-wn j i)) 0)
    (x : PairVec n) (j : Fin k) :
    let tr := preactivationTrace net (x.1-x.2) wp wn
    preP wp wn (net.decomposeWith stopPair x) j = ∑ i, ∑ path : GeometricPaths tr,
      geometricWeight tr j i path * (if geometricParity tr i path then x.2 i else x.1 i) ∧
    preN wp wn (net.decomposeWith stopPair x) j = ∑ i, ∑ path : GeometricPaths tr,
      geometricWeight tr j i path * (if geometricParity tr i path then x.1 i else x.2 i) := by
  have ht : CanonicalTrace (preactivationTrace net (x.1-x.2) wp wn) :=
    appendTrace_canonical _ _ (trace_canonical net hc _) ⟨hw,trivial⟩
  have he : pairMap wp wn (net.decomposeWith stopPair x) =
      stoppingJac (preactivationTrace net (x.1-x.2) wp wn) x := by
    rw [stopping_zeroBias_linear net hb]
    simp only [preactivationTrace,stoppingJac_appendTrace,stoppingJac,
      ContinuousLinearMap.id_comp,ungated_stopLayerJac,ContinuousLinearMap.comp_apply]
  have h := stoppingJac_geometric_paths _ ht x j
  rw [← he] at h
  exact h

/-- Bias-stub path extension: the same parity-sorted input paths plus one
explicit propagated contribution for each intermediate-layer split bias. -/
theorem stopping_biased_parity_paths {n m} (net : Network n m) (hc : net.Canonical)
    (x : PairVec n) (j : Fin m) :
    let tr := net.originalTrace (x.1-x.2)
    (net.decomposeWith stopPair x).1 j =
      (∑ i, ∑ path : GeometricPaths tr,
        geometricWeight tr j i path * (if geometricParity tr i path then x.2 i else x.1 i)) +
        ((biasSources net (x.1-x.2)).sum).1 j ∧
    (net.decomposeWith stopPair x).2 j =
      (∑ i, ∑ path : GeometricPaths tr,
        geometricWeight tr j i path * (if geometricParity tr i path then x.1 i else x.2 i)) +
        ((biasSources net (x.1-x.2)).sum).2 j := by
  have h := stoppingJac_geometric_paths _ (trace_canonical net hc (x.1-x.2)) x j
  rw [stopping_input_and_bias_sources]
  exact ⟨congrArg (fun z => z+((biasSources net (x.1-x.2)).sum).1 j) h.1,
    congrArg (fun z => z+((biasSources net (x.1-x.2)).sum).2 j) h.2⟩

end Thesis.StoppingStructure
