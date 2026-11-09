import Thesis.RoutingExtended
import Thesis.RoutingNetwork
import Thesis.RoutingProfiles
set_option pp.universes true
set_option pp.explicit true

noncomputable section
open Finset Thesis.RoutingExtended
example : ∀ (w : ℝ) (hw : 0 ≤ w) (v : WithBot ℝ),
    Thesis.RoutingGate.logCoordinate (w * expZero v) =
      Thesis.RoutingGate.logCoordinate w + v := @Thesis.RoutingExtended.source_edge_score
#check @Thesis.RoutingExtended.source_edge_score
#print axioms Thesis.RoutingExtended.source_edge_score
end

noncomputable section
universe u
open Finset Thesis.RoutingExtended
example : ∀ {A : Type u} [Fintype A] (θ : ℝ) (p : Policy A),
    Monotone (fun m => routedMass θ m p) := @Thesis.RoutingExtended.routedMass_monotone
#check @Thesis.RoutingExtended.routedMass_monotone
#print axioms Thesis.RoutingExtended.routedMass_monotone
end

noncomputable section
universe u
open Finset Thesis.RoutingExtended
example : ∀ {A : Type u} [Fintype A] [DecidableEq A] (θ : ℝ) (hθ : 0 < θ)
    (m : A → ℝ) (outside : A) (p : Policy A),
    sourceValue θ m p ≤ sourceValue θ m (gibbs θ m outside) := @Thesis.RoutingExtended.sourceValue_gibbs_optimal
#check @Thesis.RoutingExtended.sourceValue_gibbs_optimal
#print axioms Thesis.RoutingExtended.sourceValue_gibbs_optimal
end

noncomputable section
universe u
open Finset Thesis.RoutingExtended
example : ∀ {A : Type u} [Fintype A] [DecidableEq A] (m : A → ℝ) (hm : ∀ i, 0 ≤ m i) (outside : A),
    routedMass 1 m (gibbs 1 m outside) = ∑ i, m i := @Thesis.RoutingExtended.gibbs_anchor_mass
#check @Thesis.RoutingExtended.gibbs_anchor_mass
#print axioms Thesis.RoutingExtended.gibbs_anchor_mass
end

noncomputable section
universe u
open Finset Thesis.RoutingExtended
example : ∀ {A : Type u} [Fintype A] [DecidableEq A] (m : A → ℝ) (hm : ∀ i, 0 ≤ m i)
    (outside i : A) (hi : i ≠ outside),
    (gibbs 1 m outside).prob i = m i / ∑ j, m j := @Thesis.RoutingExtended.gibbs_anchor_nonoutside
#check @Thesis.RoutingExtended.gibbs_anchor_nonoutside
#print axioms Thesis.RoutingExtended.gibbs_anchor_nonoutside
end

noncomputable section
universe u
open Finset Thesis.RoutingExtended
example : ∀ {A : Type u} [Fintype A] (θ : ℝ) (m : A → ℝ) (p : Policy A) (hm : ∀ i, m i ≤ 0),
    sourceValue θ m p = ⊥ ∧ routedMass θ m p = 0 := @Thesis.RoutingExtended.empty_stream_value
#check @Thesis.RoutingExtended.empty_stream_value
#print axioms Thesis.RoutingExtended.empty_stream_value
end

noncomputable section
universe u
open Finset Thesis.RoutingExtended
example : ∀ {A : Type u} [Fintype A] [DecidableEq A] (θ : ℝ) (m : A → ℝ) (outside : A)
    (hm : ∀ i, m i ≤ 0),
    gibbs θ m outside = pure outside := @Thesis.RoutingExtended.empty_stream_absorbs
#check @Thesis.RoutingExtended.empty_stream_absorbs
#print axioms Thesis.RoutingExtended.empty_stream_absorbs
end

noncomputable section
open Thesis.RoutingExtended Thesis.RoutingProfiles
example : ∀ (θ : ℝ) (hθ : 0 < θ) (t : Tree) (plus minus : Strategy t),
    auxiliary θ t plus (canonical θ t) ≤ value θ t ∧
      value θ t ≤ auxiliary θ t (canonical θ t) minus := @Thesis.RoutingProfiles.auxiliary_saddle
#check @Thesis.RoutingProfiles.auxiliary_saddle
#print axioms Thesis.RoutingProfiles.auxiliary_saddle
end

noncomputable section
open Thesis.RoutingExtended Thesis.RoutingProfiles
example : ∀ (θ : ℝ) (t : Tree) (plus minus : Strategy t),
    reported θ t plus minus =
      (Thesis.RoutingGate.logCoordinate (auxiliary θ t plus minus),
       Thesis.RoutingGate.logCoordinate (-auxiliary θ t plus minus)) := @Thesis.RoutingProfiles.reported_coordinates
#check @Thesis.RoutingProfiles.reported_coordinates
#print axioms Thesis.RoutingProfiles.reported_coordinates
end

noncomputable section
open Thesis.RoutingExtended Thesis.RoutingProfiles
example : ∀ (θ : ℝ) (t : Tree) (plus minus : Strategy t),
    auxiliary θ t plus minus =
      expZero (reported θ t plus minus).1 - expZero (reported θ t plus minus).2 := @Thesis.RoutingProfiles.auxiliary_eq_reported_difference
#check @Thesis.RoutingProfiles.auxiliary_eq_reported_difference
#print axioms Thesis.RoutingProfiles.auxiliary_eq_reported_difference
end

noncomputable section
open Thesis.RoutingExtended Thesis.RoutingProfiles
example : ∀ (θ : ℝ) (hθ : 0 < θ) (t : Tree),
    IsNash θ t (canonical θ t) := @Thesis.RoutingProfiles.canonical_nash
#check @Thesis.RoutingProfiles.canonical_nash
#print axioms Thesis.RoutingProfiles.canonical_nash
end

noncomputable section
open Thesis.RoutingExtended Thesis.RoutingProfiles
example : ∀ (θ : ℝ) (hθ : 0 < θ) (t : Tree),
    IsSubgamePerfect θ t (canonical θ t) := @Thesis.RoutingProfiles.canonical_subgame_perfect
#check @Thesis.RoutingProfiles.canonical_subgame_perfect
#print axioms Thesis.RoutingProfiles.canonical_subgame_perfect
end

noncomputable section
open Thesis.RoutingExtended Thesis.RoutingProfiles
example : ∀ (θ : ℝ) (q : Bool) (p n : Tree)
    (h : signed q (value θ p + value θ n) ≤ 0),
    (canonical θ (.activation q p n)).1 = false := @Thesis.RoutingProfiles.canonical_stops_log_ties
#check @Thesis.RoutingProfiles.canonical_stops_log_ties
#print axioms Thesis.RoutingProfiles.canonical_stops_log_ties
end

noncomputable section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
example : ∀ {n} (q : Bool) (ε b : ℝ) (w a : Fin n → ℝ)
    (child : Fin n → Tree) (ha : ∀ i, 0 ≤ a i)
    (hv : ∀ i, value 1 (child i) = signed q (a i)),
    actionMass q (extend ε b w)
      (fun i => value 1 (extend (.terminal (signed q 1)) (.terminal (signed q 1)) child i)) =
      extend ε b (fun i => w i * a i) := @Thesis.RoutingNetwork.route_action_masses
#check @Thesis.RoutingNetwork.route_action_masses
#print axioms Thesis.RoutingNetwork.route_action_masses
end

noncomputable section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
example : ∀ {n} (q : Bool) (ε b : ℝ) (w a : Fin n → ℝ)
    (child : Fin n → Tree) (hε : 0 ≤ ε) (hb : 0 ≤ b) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, value 1 (child i) = signed q (a i)),
    value 1 (route q ε b w child hε hb hw) = signed q (ε + (b + ∑ i, w i * a i)) := @Thesis.RoutingNetwork.route_anchor_value
#check @Thesis.RoutingNetwork.route_anchor_value
#print axioms Thesis.RoutingNetwork.route_anchor_value
end

noncomputable section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
example : ∀ {n} (q : Bool) (ε b : ℝ) (w a : Fin n → ℝ)
    (child : Fin n → Tree) (hε : 0 ≤ ε) (hb : 0 ≤ b) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, value 1 (child i) = signed q (a i)) (i : Fin n),
    (canonical 1 (route q ε b w child hε hb hw)).1.prob i.succ.succ =
      w i * a i / (ε + (b + ∑ j, w j * a j)) := @Thesis.RoutingNetwork.route_anchor_ordinary_probability
#check @Thesis.RoutingNetwork.route_anchor_ordinary_probability
#print axioms Thesis.RoutingNetwork.route_anchor_ordinary_probability
end

noncomputable section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
example : ∀ {n m} (net : Network n m) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (q : Bool),
    value 1 (networkGame net ε hε x j q) = signed q (net.eval x j) := @Thesis.RoutingNetwork.networkGame_value
#check @Thesis.RoutingNetwork.networkGame_value
#print axioms Thesis.RoutingNetwork.networkGame_value
end

noncomputable section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
example : ∀ {n m} (net : Network n m) (θ : ℝ) (hθ : 0 < θ)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin m) (q : Bool),
    IsSubgamePerfect θ (networkGame net ε hε x j q) (canonical θ (networkGame net ε hε x j q)) := @Thesis.RoutingNetwork.networkGame_subgame_perfect
#check @Thesis.RoutingNetwork.networkGame_subgame_perfect
#print axioms Thesis.RoutingNetwork.networkGame_subgame_perfect
end

noncomputable section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
example : ∀ {n m} (net : Network n m) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (q : Bool),
    reported 1 (networkGame net ε hε x j q)
      (canonical 1 (networkGame net ε hε x j q)) (canonical 1 (networkGame net ε hε x j q)) =
      (Thesis.RoutingGate.logCoordinate (signed q (net.eval x j)),
       Thesis.RoutingGate.logCoordinate (-signed q (net.eval x j))) := @Thesis.RoutingNetwork.networkGame_reported
#check @Thesis.RoutingNetwork.networkGame_reported
#print axioms Thesis.RoutingNetwork.networkGame_reported
end

noncomputable section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
example : ∀ {n k m} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (tail : Network k m) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (q : Bool),
    reported 1 (networkGame (.layer wp wn bp bn tail) ε hε x j q)
      (canonical 1 (networkGame (.layer wp wn bp bn tail) ε hε x j q))
      (canonical 1 (networkGame (.layer wp wn bp bn tail) ε hε x j q)) =
      if q then (Thesis.RoutingGate.logCoordinate ((Network.layer wp wn bp bn tail).eval x j), ⊥)
      else (⊥, Thesis.RoutingGate.logCoordinate ((Network.layer wp wn bp bn tail).eval x j)) := @Thesis.RoutingNetwork.networkLayer_reported
#check @Thesis.RoutingNetwork.networkLayer_reported
#print axioms Thesis.RoutingNetwork.networkLayer_reported
end

noncomputable section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
example : ∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) (q : Bool),
    (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q)).1 =
      decide (0 < preactivation wp wn bp bn x j) := @Thesis.RoutingNetwork.inputLayerGames_selected_gate
#check @Thesis.RoutingNetwork.inputLayerGames_selected_gate
#print axioms Thesis.RoutingNetwork.inputLayerGames_selected_gate
end

noncomputable section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
example : ∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (input : Fin n → Bool → Tree) (x : Vec n)
    (hx : ∀ i, 0 ≤ x i) (hv : ∀ i q, value 1 (input i q) = signed q (x i))
    (j : Fin k) (q : Bool),
    (canonical 1 (layerGames wp wn bp bn ε hε input j q)).1 =
      decide (0 < preactivation wp wn bp bn x j) := @Thesis.RoutingNetwork.layerGames_selected_gate
#check @Thesis.RoutingNetwork.layerGames_selected_gate
#print axioms Thesis.RoutingNetwork.layerGames_selected_gate
end
