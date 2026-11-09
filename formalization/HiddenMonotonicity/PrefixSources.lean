import HiddenMonotonicity.AlmostEverywhere

namespace HiddenMonotonicity
open MeasureTheory

/-- Composition uses the existing varying-width network, preserving its layers. -/
def Network.append {a b c : ℕ} : Network a b → Network b c → Network a c
  | .output _, suffix => suffix
  | .layer wp wn bp bn tail, suffix => .layer wp wn bp bn (tail.append suffix)

theorem Network.append_eval {a b c : ℕ} (preNet : Network a b) (suffix : Network b c) :
    (preNet.append suffix).eval = suffix.eval ∘ preNet.eval := by
  induction preNet with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      funext x
      simpa only [Network.append, Network.eval, ih, Function.comp_apply]

theorem Network.append_nonnegative {a b c : ℕ} (preNet : Network a b) (suffix : Network b c)
    (hp : preNet.Nonnegative) (hs : suffix.Nonnegative) : (preNet.append suffix).Nonnegative := by
  induction preNet with
  | output n => exact hs
  | layer wp wn bp bn tail ih => exact ⟨hp.1,hp.2.1,ih suffix hp.2.2 hs⟩

theorem Network.append_originalJac {a b c : ℕ} (preNet : Network a b) (suffix : Network b c)
    (x : Vec a) :
    ((preNet.append suffix).originalTrace x).originalJac =
      (suffix.originalTrace (preNet.eval x)).originalJac.comp (preNet.originalTrace x).originalJac := by
  induction preNet with
  | output n => simp [Network.append, Network.eval, Network.originalTrace, MaskedTrace.originalJac]
  | layer wp wn bp bn tail ih =>
      simp only [Network.append, Network.originalTrace, MaskedTrace.originalJac, ih,
        ContinuousLinearMap.comp_assoc]
      rfl

/-- The computed original Jacobian is an actual derivative almost everywhere,
without requiring that zero-preactivation sets be null. -/
theorem Network.originalTrace_ae_derivative {n m} (net : Network n m) (hw : net.Nonnegative) :
    ∀ᵐ x : Vec n, HasFDerivAt net.eval (net.originalTrace x).originalJac x := by
  have hi (i : Fin m) := net.affine_ae_backward_invariants hw
    (ContinuousLinearMap.proj i) 0 (fun _ _ h => h i) (fun _ _ _ => le_rfl) 0 0
  have hall := (MeasureTheory.ae_all_iff).mpr hi
  filter_upwards [hall] with x hx
  have hd : HasFDerivAt net.eval
      (ContinuousLinearMap.pi fun i => (ContinuousLinearMap.proj i).comp (net.originalTrace x).originalJac) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    have h := (hx i (fun _ => 0) 0).1
    change HasFDerivAt (fun y => ((ContinuousLinearMap.proj i : Row m)-0) (net.eval y)+(0-0)) _ x at h
    simpa using h
  convert hd using 1
  ext v i
  rfl

theorem minLayer_eq_affine_sub_relu {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : Vec n) :
    minLayer wp wn bp bn x = affineLayer wp wn bp bn x-reluLayer wp wn bp bn x := by
  funext i
  change min (affineLayer wp wn bp bn x i) 0 =
    affineLayer wp wn bp bn x i-max (affineLayer wp wn bp bn x i) 0
  rcases le_total (affineLayer wp wn bp bn x i) 0 with h | h
  · rw [min_eq_left h,max_eq_right h]; ring
  · rw [min_eq_right h,max_eq_left h]; ring

theorem deadMap_eq_sub {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (gate : Fin k → Bool) :
    MaskedTrace.deadMap wp wn gate = matrixCLM (wp-wn)-MaskedTrace.signedMap wp wn gate := by
  ext v i
  simp [MaskedTrace.deadMap, MaskedTrace.inactiveMap, MaskedTrace.signedMap]

/-- A minimum source is preactivation minus the next original ReLU preNet.
Both preNet derivatives exist almost everywhere, including degenerate gates. -/
theorem Network.prefix_minimum_ae_derivative {a n k} (preNet : Network a n)
    (hp : preNet.Nonnegative) (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (hw : ∀ i j, 0≤wp i j ∧ 0≤wn i j) :
    ∀ᵐ x : Vec a, HasFDerivAt (minLayer wp wn bp bn ∘ preNet.eval)
      ((MaskedTrace.deadMap wp wn (originalGate wp wn bp bn (preNet.eval x))).comp
        (preNet.originalTrace x).originalJac) x := by
  let next := preNet.append (.layer wp wn bp bn (.output k))
  have hn : next.Nonnegative := preNet.append_nonnegative _ hp
    ⟨fun i j => (hw i j).1, fun i j => (hw i j).2, trivial⟩
  have he : next.eval = reluLayer wp wn bp bn ∘ preNet.eval := by
    rw [show next=preNet.append (.layer wp wn bp bn (.output k)) from rfl, preNet.append_eval]
    rfl
  have hj (x : Vec a) : (next.originalTrace x).originalJac =
      (MaskedTrace.signedMap wp wn (originalGate wp wn bp bn (preNet.eval x))).comp
        (preNet.originalTrace x).originalJac := by
    rw [show next=preNet.append (.layer wp wn bp bn (.output k)) from rfl,
      preNet.append_originalJac]
    simp only [Network.originalTrace, MaskedTrace.originalJac, ContinuousLinearMap.id_comp]
  filter_upwards [preNet.originalTrace_ae_derivative hp, next.originalTrace_ae_derivative hn] with x hx hnext
  rw [he,hj] at hnext
  have hz := (affineLayer_hasFDerivAt wp wn bp bn (preNet.eval x)).comp x hx
  have hd := hz.fun_sub hnext
  have hf : (fun y => (affineLayer wp wn bp bn ∘ preNet.eval) y-
      (reluLayer wp wn bp bn ∘ preNet.eval) y) = minLayer wp wn bp bn ∘ preNet.eval := by
    funext y
    exact (minLayer_eq_affine_sub_relu wp wn bp bn (preNet.eval y)).symm
  rw [hf] at hd
  rw [deadMap_eq_sub, ContinuousLinearMap.sub_comp]
  exact hd

/-- Prefix-generalized Q derivative theorem. Induction appends to the preNet,
so Rademacher is applied in the original input space, never to a pushforward
measure that could concentrate on an internal kink hyperplane. -/
theorem Network.qSources_after_prefix_ae {a n m} (net : Network n m)
    (hw : net.Nonnegative) (preNet : Network a n) (hp : preNet.Nonnegative) (α : ℕ → ℝ) :
    ∀ᵐ x : Vec a, ∀ q ∈ net.qSources (preNet.eval x) α,
      HasFDerivAt (q.value ∘ preNet.eval)
        (q.jacobian.comp (preNet.originalTrace x).originalJac) x := by
  induction net generalizing a α with
  | output n => simp [Network.qSources]
  | @layer n k m wp wn bp bn tail ih =>
      let next := preNet.append (.layer wp wn bp bn (.output k))
      have hn : next.Nonnegative := preNet.append_nonnegative _ hp ⟨hw.1,hw.2.1,trivial⟩
      have he : next.eval = reluLayer wp wn bp bn ∘ preNet.eval := by
        rw [show next=preNet.append (.layer wp wn bp bn (.output k)) from rfl, preNet.append_eval]
        rfl
      have hj (x : Vec a) : (next.originalTrace x).originalJac =
          (MaskedTrace.signedMap wp wn (originalGate wp wn bp bn (preNet.eval x))).comp
            (preNet.originalTrace x).originalJac := by
        rw [show next=preNet.append (.layer wp wn bp bn (.output k)) from rfl, preNet.append_originalJac]
        simp only [Network.originalTrace, MaskedTrace.originalJac, ContinuousLinearMap.id_comp]
      have hmin := preNet.prefix_minimum_ae_derivative hp wp wn bp bn
        (fun i j => ⟨hw.1 i j,hw.2.1 i j⟩)
      have htail := ih hw.2.2 next hn (fun i => α (i+1))
      filter_upwards [hmin,htail] with x hx htx
      intro q hq
      simp only [Network.qSources, List.mem_cons, List.mem_map] at hq
      rcases hq with hq | ⟨q',hq',rfl⟩
      · subst q
        simpa only [QSource.value, QSource.jacobian, ContinuousLinearMap.comp_assoc, Function.comp_def]
          using tail.absCLM.hasFDerivAt.comp x hx
      · rw [he] at htx
        have ht := htx q' hq'
        rw [hj] at ht
        simpa only [QSource.pull, ContinuousLinearMap.comp_assoc, Function.comp_assoc] using ht

theorem Network.qSources_ae_derivatives {n m} (net : Network n m)
    (hw : net.Nonnegative) (α : ℕ → ℝ) :
    ∀ᵐ x : Vec n, ∀ q ∈ net.qSources x α, HasFDerivAt q.value q.jacobian x := by
  have h := net.qSources_after_prefix_ae hw (.output n) trivial α
  simpa only [Network.eval, Network.originalTrace, MaskedTrace.originalJac,
    ContinuousLinearMap.comp_id, Function.comp_def] using h

theorem Network.absoluteQSources_ae_derivatives {n m} (net : Network n m)
    (hc : net.Canonical) (α : ℕ → ℝ) :
    ∀ᵐ x : Vec n, ∀ q ∈ net.absoluteQSources x α, HasFDerivAt q.value q.jacobian x := by
  have h := net.qSources_ae_derivatives (net.canonical_nonnegative hc) α
  simpa only [net.qSources_eq_absolute hc] using h

end HiddenMonotonicity
