import Thesis.CPWLLattice
import Mathlib.Data.Nat.Log

/-! Explicit bounded-depth max-affine trees in the shared varying-width Network.
Affine readouts carry signed intermediate values without adding hidden layers. -/
noncomputable section
namespace Thesis.ReLURepresentation
open HiddenMonotonicity Thesis.Tropical Matrix Finset

def hiddenDepth {n m} : Network n m → ℕ
  | .output _ => 0
  | .layer _ _ _ _ tail => hiddenDepth tail+1

def concatenate {n m k} : Network n m → Network m k → Network n k
  | .output _, right => right
  | .layer wp wn bp bn tail, right => .layer wp wn bp bn (concatenate tail right)

theorem concatenate_eval {n m k} (left : Network n m) (right : Network m k) (x : Fin n → ℝ) :
    (concatenate left right).eval x=right.eval (left.eval x) := by
  induction left with
  | output => rfl
  | layer wp wn bp bn tail ih => exact ih right _

theorem concatenate_depth {n m k} (left : Network n m) (right : Network m k) :
    hiddenDepth (concatenate left right)=hiddenDepth left+hiddenDepth right := by
  induction left with
  | output => simp [concatenate,hiddenDepth]
  | layer wp wn bp bn tail ih => simp [concatenate,hiddenDepth,ih]; omega

/-- Actual shared-network data followed by an arbitrary affine readout. -/
structure AffineHead (n : ℕ) (O : Type) where
  width : ℕ
  network : Network n width
  weights : Matrix O (Fin width) ℝ
  bias : O → ℝ

def AffineHead.eval {n O} (H : AffineHead n O) (x : Fin n → ℝ) : O → ℝ :=
  H.weights.mulVec (H.network.eval x)+H.bias

def AffineHead.depth {n O} (H : AffineHead n O) : ℕ := hiddenDepth H.network

def affineHead {n O} (w : Matrix O (Fin n) ℝ) (b : O → ℝ) : AffineHead n O :=
  ⟨n,.output n,w,b⟩

theorem affineHead_eval {n O} (w : Matrix O (Fin n) ℝ) (b : O → ℝ) (x : Fin n → ℝ) :
    (affineHead w b).eval x=w.mulVec x+b := rfl

def maxRows {O : Type} (v : O × Bool → ℝ) (r : O × Fin 3) : ℝ :=
  if r.2=0 then v (r.1,false)-v (r.1,true) else
  if r.2=1 then v (r.1,true) else -v (r.1,true)

def maxReadout {O : Type} [DecidableEq O] (i : O) (r : O × Fin 3) : ℝ :=
  if r.1=i then (if r.2=2 then -1 else 1) else 0

theorem max_rails (u v : ℝ) : relu (u-v)+relu v-relu (-v)=max u v := by
  have hv := (canonical_weight_split v).1
  have hh := max_sub_sub_right u v v
  simp only [sub_self] at hh
  dsimp [relu]
  linarith

def AffineHead.pairwiseMax {n O} [Fintype O] [DecidableEq O]
    (H : AffineHead n (O × Bool)) : AffineHead n O :=
  let e := Fintype.equivFin (O × Fin 3)
  let w : Matrix (Fin (Fintype.card (O × Fin 3))) (Fin H.width) ℝ :=
    fun r j => maxRows (fun i => H.weights i j) (e.symm r)
  let b : Fin (Fintype.card (O × Fin 3)) → ℝ := fun r => maxRows H.bias (e.symm r)
  { width := Fintype.card (O × Fin 3)
    network := concatenate H.network (.layer w 0 b 0 (.output _))
    weights := fun i r => maxReadout i (e.symm r)
    bias := 0 }

private theorem maxRows_affine {m O} (W : Matrix (O × Bool) (Fin m) ℝ)
    (b : O × Bool → ℝ) (x : Fin m → ℝ) (r : O × Fin 3) :
    (∑ j, maxRows (fun i => W i j) r*x j)+maxRows b r=maxRows (W.mulVec x+b) r := by
  unfold maxRows
  split_ifs <;> simp [mulVec,dotProduct,sub_mul,neg_mul,sum_sub_distrib,sum_neg_distrib] <;> ring

set_option backward.isDefEq.respectTransparency false in
theorem AffineHead.pairwiseMax_eval {n O} [Fintype O] [DecidableEq O]
    (H : AffineHead n (O × Bool)) (x : Fin n → ℝ) (i : O) :
    H.pairwiseMax.eval x i=max (H.eval x (i,false)) (H.eval x (i,true)) := by
  let e := Fintype.equivFin (O × Fin 3)
  have hsum (v : O × Fin 3 → ℝ) : (∑ j : Fin (Fintype.card (O × Fin 3)), v (e.symm j))=∑ r,v r :=
    e.symm.sum_comp v
  have hn (r : Fin (Fintype.card (O × Fin 3))) :
      H.pairwiseMax.network.eval x r=relu (maxRows (H.eval x) (e.symm r)) := by
    change (concatenate H.network (.layer (fun r k => maxRows (fun a => H.weights a k) (e.symm r)) 0
      (fun r => maxRows H.bias (e.symm r)) 0 (.output _))).eval x r=_
    rw [concatenate_eval]
    simp only [Network.eval,Pi.add_apply,mulVec,dotProduct,sub_zero]
    change relu ((∑ j, maxRows (fun a => H.weights a j) (e.symm r)*H.network.eval x j)+
      maxRows H.bias (e.symm r))=_
    congr 1
    exact maxRows_affine H.weights H.bias (H.network.eval x) (e.symm r)
  change (∑ j, maxReadout i (e.symm j)*H.pairwiseMax.network.eval x j)+0=_
  simp_rw [hn]
  rw [add_zero,hsum (fun r => maxReadout i r*relu (maxRows (H.eval x) r))]
  simp only [Fintype.sum_prod_type]
  simp [maxReadout,maxRows,Fin.sum_univ_succ,← max_rails]
  ring

theorem AffineHead.pairwiseMax_depth {n O} [Fintype O] [DecidableEq O]
    (H : AffineHead n (O × Bool)) : H.pairwiseMax.depth=H.depth+1 := by
  simp [pairwiseMax,depth,concatenate_depth,hiddenDepth]



/-- Splitting binary strings partitions their finite maximum into two child maxima. -/
theorem finiteMax_bits_succ (k : ℕ) (v : (Fin (k+1) → Bool) → ℝ) :
    finiteMax v=max (finiteMax (fun t => v (Fin.cons false t)))
      (finiteMax (fun t => v (Fin.cons true t))) := by
  apply le_antisymm
  · apply finiteMax_le
    intro t
    have ht := Fin.cons_self_tail t
    cases h : t 0
    · have hh := le_finiteMax (fun s => v (Fin.cons false s)) (Fin.tail t)
      have ht' : Fin.cons false (Fin.tail t)=t := by simpa only [h] using ht
      rw [ht'] at hh
      exact hh.trans (le_max_left _ _)
    · have hh := le_finiteMax (fun s => v (Fin.cons true s)) (Fin.tail t)
      have ht' : Fin.cons true (Fin.tail t)=t := by simpa only [h] using ht
      rw [ht'] at hh
      exact hh.trans (le_max_right _ _)
  · apply max_le
    · exact finiteMax_le _ _ (fun t => le_finiteMax v (Fin.cons false t))
    · exact finiteMax_le _ _ (fun t => le_finiteMax v (Fin.cons true t))

/-- A whole finite forest of affine maxima, each with 2^k leaves, is compiled
into one shared varying-width network with exactly k hidden ReLU layers. -/
theorem affine_max_forest {n : ℕ} (k : ℕ) (O : Type) [Fintype O]
    (w : O → (Fin k → Bool) → Fin n → ℝ) (b : O → (Fin k → Bool) → ℝ) :
    ∃ H : AffineHead n O, H.depth=k ∧
      ∀ x i, H.eval x i=finiteMax (fun t => w i t ⬝ᵥ x+b i t) := by
  classical
  induction k generalizing O with
  | zero =>
      let t : Fin 0 → Bool := Fin.elim0
      refine ⟨affineHead (fun i => w i t) (fun i => b i t),rfl,?_⟩
      intro x i
      change w i t ⬝ᵥ x+b i t=finiteMax _
      apply le_antisymm
      · exact le_finiteMax (fun t => w i t ⬝ᵥ x+b i t) t
      · exact finiteMax_le _ _ (fun s => by rw [Subsingleton.elim s t])
  | succ k ih =>
      obtain ⟨H,hdepth,he⟩ := ih (O × Bool)
        (fun i t => w i.1 (Fin.cons i.2 t)) (fun i t => b i.1 (Fin.cons i.2 t))
      refine ⟨H.pairwiseMax,?_,?_⟩
      · rw [AffineHead.pairwiseMax_depth,hdepth]
      · intro x i
        rw [AffineHead.pairwiseMax_eval,he,he,finiteMax_bits_succ]

/-- Padding an arbitrary finite nonempty term type to a binary tree preserves
its maximum. This supplies a real network even when the term count is not a power of two. -/
theorem polynomial_forest {n k : ℕ} (O : Type) [Fintype O]
    (p : O → Thesis.Tropical.Polynomial (Fin n))
    (hcard : ∀ i, Fintype.card (p i).Terms≤2^k) :
    ∃ H : AffineHead n O, H.depth=k ∧ ∀ x i, H.eval x i=(p i).eval x := by
  classical
  have hbits : Fintype.card (Fin k → Bool)=2^k := by simp
  have hemb (i : O) : Nonempty ((p i).Terms ↪ (Fin k → Bool)) :=
    Function.Embedding.nonempty_of_card_le (by rw [hbits]; exact hcard i)
  let emb := fun i => Classical.choice (hemb i)
  let pad := fun i => Function.invFun (emb i)
  have hpad (i : O) : Function.Surjective (pad i) :=
    (Function.leftInverse_invFun (emb i).injective).surjective
  obtain ⟨H,hd,he⟩ := affine_max_forest k O
    (fun i t => (p i).slope (pad i t)) (fun i t => (p i).intercept (pad i t))
  refine ⟨H,hd,?_⟩
  intro x i
  rw [he]
  apply le_antisymm
  · exact finiteMax_le _ _ (fun t => le_finiteMax (fun a => (p i).slope a ⬝ᵥ x+(p i).intercept a) (pad i t))
  · apply finiteMax_le
    intro a
    obtain ⟨t,ht⟩ := hpad i a
    rw [← ht]
    exact le_finiteMax (fun s => (p i).slope (pad i s) ⬝ᵥ x+(p i).intercept (pad i s)) t



/-- An arbitrary finite signed linear combination is absorbed into the affine
readout and does not introduce an additional hidden layer. -/
def AffineHead.linearCombination {n O} [Fintype O] (H : AffineHead n O) (c : O → ℝ) :
    AffineHead n Unit where
  width := H.width
  network := H.network
  weights := fun _ j => ∑ i, c i*H.weights i j
  bias := fun _ => ∑ i, c i*H.bias i

theorem AffineHead.linearCombination_eval {n O} [Fintype O]
    (H : AffineHead n O) (c : O → ℝ) (x : Fin n → ℝ) :
    (H.linearCombination c).eval x ()=∑ i, c i*H.eval x i := by
  simp only [linearCombination,eval,mulVec,dotProduct,Pi.add_apply,
    Finset.sum_mul,Finset.mul_sum,mul_add,Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem AffineHead.linearCombination_depth {n O} [Fintype O]
    (H : AffineHead n O) (c : O → ℝ) : (H.linearCombination c).depth=H.depth := rfl

/-- Complete compiler for a finite signed sum of max-affine polynomials with at
most 2^k terms each. It produces the shared Network with an actual affine readout. -/
theorem signed_polynomial_compiler {n k : ℕ} (O : Type) [Fintype O]
    (p : O → Thesis.Tropical.Polynomial (Fin n)) (c : O → ℝ)
    (hcard : ∀ i, Fintype.card (p i).Terms≤2^k) :
    ∃ H : AffineHead n Unit, H.depth=k ∧
      ∀ x, H.eval x ()=∑ i, c i*(p i).eval x := by
  obtain ⟨H,hd,he⟩ := polynomial_forest O p hcard
  refine ⟨H.linearCombination c,hd,?_⟩
  intro x
  rw [AffineHead.linearCombination_eval]
  exact sum_congr rfl (fun i _ => congrArg (fun y => c i*y) (he x i))

end Thesis.ReLURepresentation
