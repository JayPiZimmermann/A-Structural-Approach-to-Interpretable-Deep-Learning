import HiddenMonotonicity.ConvexInput
set_option pp.explicit true
set_option pp.universes true

noncomputable section
open Set HiddenMonotonicity
example : (∀ {d n m : ℕ} (net : Network n m) (hw : net.Nonnegative)
(p q : Vec d → Vec n)
(hp : ∀ i, ConvexOn ℝ univ (fun x => p x i))
(hq : ∀ i, ConvexOn ℝ univ (fun x => q x i)),
(∀ i, ConvexOn ℝ univ (fun x => (net.split (p x) (q x)).1 i)) ∧
(∀ i, ConvexOn ℝ univ (fun x => (net.split (p x) (q x)).2 i))) := @HiddenMonotonicity.Network.split_convex_input
#check @HiddenMonotonicity.Network.split_convex_input
#print axioms HiddenMonotonicity.Network.split_convex_input
end

noncomputable section
open Set HiddenMonotonicity
example : (∀ {d n m : ℕ} (net : Network n m) (hw : net.Nonnegative)
(p q : Vec d → Vec n)
(hp : ∀ i, ConvexOn ℝ univ (fun x => p x i))
(hq : ∀ i, ConvexOn ℝ univ (fun x => q x i))
(wp wn : Vec m) (hwp : ∀ i, 0 ≤ wp i) (hwn : ∀ i, 0 ≤ wn i) (bp bn : ℝ),
ConvexOn ℝ univ (fun x => (net.affineHeads (coefficientRow wp) (coefficientRow wn) bp bn (p x,q x)).1) ∧
ConvexOn ℝ univ (fun x => (net.affineHeads (coefficientRow wp) (coefficientRow wn) bp bn (p x,q x)).2)) := @HiddenMonotonicity.Network.affine_heads_convex_input
#check @HiddenMonotonicity.Network.affine_heads_convex_input
#print axioms HiddenMonotonicity.Network.affine_heads_convex_input
end

noncomputable section
open Set HiddenMonotonicity
example : (∀ {d n m : ℕ} (net : Network n m) (hw : net.Nonnegative)
(p q : Vec d → Vec n)
(hp : ∀ i, ConvexOn ℝ univ (fun x => p x i))
(hq : ∀ i, ConvexOn ℝ univ (fun x => q x i)),
(∀ i, ConvexOn ℝ univ (fun x => (net.decomposeWith (mixPair 1) (p x,q x)).1 i)) ∧
(∀ i, ConvexOn ℝ univ (fun x => (net.decomposeWith (mixPair 1) (p x,q x)).2 i)) ∧
(∀ x, (net.decomposeWith (mixPair 1) (p x,q x)).1 - (net.decomposeWith (mixPair 1) (p x,q x)).2 = net.eval (p x-q x))) := @HiddenMonotonicity.Network.mixing_one_convex_input
#check @HiddenMonotonicity.Network.mixing_one_convex_input
#print axioms HiddenMonotonicity.Network.mixing_one_convex_input
end
