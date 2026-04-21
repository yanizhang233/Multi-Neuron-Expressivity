import MultiNeuron.Relaxation.Crosslayer
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set

namespace Net

noncomputable section

/-!
This file formalizes the fixed-radius sliding-window version of Lemma 4.1.
-/

/-- Project a set of vectors to the `o`-th coordinate. -/
def proj {m : Nat} (o : Fin m) (S : Set (Coord m)) : Set Real :=
  (fun y => y o) '' S

noncomputable def lbproj {m : Nat} (o : Fin m) (S : Set (Coord m)) : Real :=
  sInf (proj o S)

noncomputable def ubproj {m : Nat} (o : Fin m) (S : Set (Coord m)) : Real :=
  sSup (proj o S)

/-- Projecting a nonempty set to a coordinate still gives a nonempty set. -/
theorem proj_nonempty {m : Nat} (o : Fin m) {S : Set (Coord m)} (hS : S.Nonempty) :
    (proj o S).Nonempty := by
  rcases hS with ⟨x, hx⟩
  exact ⟨x o, ⟨x, hx, rfl⟩⟩

/-- The convex hull of a nonempty set is nonempty. -/
theorem convexHull_nonempty {m : Nat} {S : Set (Coord m)} (hS : S.Nonempty) :
    (convexHull Real S).Nonempty := by
  rcases hS with ⟨x, hx⟩
  exact ⟨x, subset_convexHull Real S hx⟩

private theorem isBounded_image_of_continuous {n m : Nat} {S : Set (Coord n)}
    {f : Coord n → Coord m} (hf : Continuous f) (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (f '' S) := by
  letI : ProperSpace (Coord n) := FiniteDimensional.proper ℝ (Coord n)
  exact ((hS.isCompact_closure.image hf).isBounded).subset (image_mono subset_closure)

theorem WholeNetConvexRelax_bounded {n m : Nat} (f : Net n m) {X : Set (Coord n)}
    (hX : Bornology.IsBounded X) :
    Bornology.IsBounded (WholeNetConvexRelax f X) := by
  rw [WholeNetConvexRelax_eq_convexHull_reach]
  have hImg : Bornology.IsBounded (reach f X) := by
    simpa [Net.reach] using isBounded_image_of_continuous (continuous_eval f) hX
  exact (isBounded_convexHull : Bornology.IsBounded (convexHull ℝ (reach f X)) ↔ _).2 hImg

/-- Lower bound returned by the actual sliding-window `P_r` relaxation. -/
noncomputable def lbPrActual {r n m : Nat}
    (hr : 0 < r) (f : Net n m) (X : Polytope n) (o : Fin m) : Real :=
  lbproj o (PrOutputSetOnPolytope hr f X)

/-- Upper bound returned by the actual sliding-window `P_r` relaxation. -/
noncomputable def ubPrActual {r n m : Nat}
    (hr : 0 < r) (f : Net n m) (X : Polytope n) (o : Fin m) : Real :=
  ubproj o (PrOutputSetOnPolytope hr f X)

/--
The remaining trace-gluing hypothesis needed to bridge the pumped
sliding-window relaxation.
-/
def PumpGlueCondition {d d' k : Nat} {r : Nat}
    (hr : 0 < r) (f₁ : Net d d') (f₂ : Net d' k) (X : Set (Coord d)) : Prop :=
  let left : LayerChain.T d d' :=
    LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r)
  let right : LayerChain.T d' k :=
    LayerChain.appendChain (LayerChain.idChain d' r) (LayerChain.FlattenNet f₂)
  let whole : LayerChain.T d k := LayerChain.appendChain left right
  ∀ {u : FullTrace left} {v : FullTrace right},
    u ∈ convHullTrace left X →
    v ∈ PrRelaxedSetChain r hr right {traceOutput u} →
    LayerChain.spliceTrace u v ∈ PrRelaxedSetChain r hr whole X

/--
The pumped sliding-window relaxation contains the middle-convexified reach set,
assuming the explicit trace-gluing condition.
-/
theorem reach_conv_middle_subset_PrOutputSet_pump
    {d d' k : Nat} {r : Nat} (hr : 0 < r)
    (f₁ : Net d d') (f₂ : Net d' k) (X : Set (Coord d))
    (hglue : PumpGlueCondition hr f₁ f₂ X) :
    reach f₂ (convexHull Real (reach f₁ X)) ⊆
      PrOutputSet hr (pumpNetPr f₁ f₂ r) X := by
  simpa [PumpGlueCondition] using
    (reach_conv_middle_subset_PrOutputSet_pump_of_glue hr f₁ f₂ X hglue)

/--
lower-bound half of Lemma 4.1.
-/
theorem lemma41_lower
    {d d' : Nat} (α : Real) (hα : α < 1)
    (f₁ : Net d d') (f₂ : Net d' 1) (s : Nat) (X : Set (Coord d))
    (hXne : X.Nonempty)
    (hlarge :
      let r := alphaRadius α (layerCount (pumpNetPr f₁ f₂ s))
      r ≤ s)
    (hglue :
      let r := alphaRadius α (layerCount (pumpNetPr f₁ f₂ s))
      let hr : 0 < r := alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s))
      let f₂' := prependIds (2 * (s - r)) f₂
      let left : LayerChain.T d d' :=
        LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r)
      let right : LayerChain.T d' 1 :=
        LayerChain.appendChain (LayerChain.idChain d' r) (LayerChain.FlattenNet f₂')
      let whole : LayerChain.T d 1 := LayerChain.appendChain left right
      ∀ {u : FullTrace left} {v : FullTrace right},
        u ∈ convHullTrace left X →
        v ∈ PrRelaxedSetChain r hr right {traceOutput u} →
        LayerChain.spliceTrace u v ∈ PrRelaxedSetChain r hr whole X)
    (hPr_bdd :
      Bornology.IsBounded
        (PrOutputSet
          (alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s)))
          (pumpNetPr f₁ f₂ s) X)) :
    lbproj 0 (reach f₂ (convexHull Real (reach f₁ X))) ≥
      lbproj 0
        (PrOutputSet
          (alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s)))
          (pumpNetPr f₁ f₂ s) X) := by
  let hr : 0 < alphaRadius α (layerCount (pumpNetPr f₁ f₂ s)) :=
    alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s))
  let S := proj 0 (reach f₂ (convexHull Real (reach f₁ X)))
  let T := proj 0 (PrOutputSet hr (pumpNetPr f₁ f₂ s) X)
  have hbridge :
      reach f₂ (convexHull Real (reach f₁ X)) ⊆
        PrOutputSet hr (pumpNetPr f₁ f₂ s) X := by
    simpa [hr] using
      reach_conv_middle_subset_PrOutputSet_pump_of_glue_radius α hα f₁ f₂ s X hlarge hglue
  have hST : S ⊆ T := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact ⟨y, hbridge hy, rfl⟩
  have hS_nonempty : S.Nonempty := by
    apply proj_nonempty 0
    apply reach_nonempty
    apply convexHull_nonempty
    exact reach_nonempty f₁ hXne
  have hT_bddBelow : BddBelow T := hPr_bdd.image_eval 0 |>.bddBelow
  have hmain :
      lbproj 0 (PrOutputSet hr (pumpNetPr f₁ f₂ s) X) ≤
        lbproj 0 (reach f₂ (convexHull Real (reach f₁ X))) := by
    simpa [lbproj, S, T] using csInf_le_csInf hT_bddBelow hS_nonempty hST
  simpa [ge_iff_le, hr] using hmain

/--
 upper-bound half of Lemma 4.1.
-/
theorem lemma41_upper
    {d d' : Nat} (α : Real) (hα : α < 1)
    (f₁ : Net d d') (f₂ : Net d' 1) (s : Nat) (X : Set (Coord d))
    (hXne : X.Nonempty)
    (hlarge :
      let r := alphaRadius α (layerCount (pumpNetPr f₁ f₂ s))
      r ≤ s)
    (hglue :
      let r := alphaRadius α (layerCount (pumpNetPr f₁ f₂ s))
      let hr : 0 < r := alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s))
      let f₂' := prependIds (2 * (s - r)) f₂
      let left : LayerChain.T d d' :=
        LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r)
      let right : LayerChain.T d' 1 :=
        LayerChain.appendChain (LayerChain.idChain d' r) (LayerChain.FlattenNet f₂')
      let whole : LayerChain.T d 1 := LayerChain.appendChain left right
      ∀ {u : FullTrace left} {v : FullTrace right},
        u ∈ convHullTrace left X →
        v ∈ PrRelaxedSetChain r hr right {traceOutput u} →
        LayerChain.spliceTrace u v ∈ PrRelaxedSetChain r hr whole X)
    (hPr_bdd :
      Bornology.IsBounded
        (PrOutputSet
          (alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s)))
          (pumpNetPr f₁ f₂ s) X)) :
    ubproj 0 (reach f₂ (convexHull Real (reach f₁ X))) ≤
      ubproj 0
        (PrOutputSet
          (alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s)))
          (pumpNetPr f₁ f₂ s) X) := by
  let hr : 0 < alphaRadius α (layerCount (pumpNetPr f₁ f₂ s)) :=
    alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s))
  let S := proj 0 (reach f₂ (convexHull Real (reach f₁ X)))
  let T := proj 0 (PrOutputSet hr (pumpNetPr f₁ f₂ s) X)
  have hbridge :
      reach f₂ (convexHull Real (reach f₁ X)) ⊆
        PrOutputSet hr (pumpNetPr f₁ f₂ s) X := by
    simpa [hr] using
      reach_conv_middle_subset_PrOutputSet_pump_of_glue_radius α hα f₁ f₂ s X hlarge hglue
  have hST : S ⊆ T := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact ⟨y, hbridge hy, rfl⟩
  have hS_nonempty : S.Nonempty := by
    apply proj_nonempty 0
    apply reach_nonempty
    apply convexHull_nonempty
    exact reach_nonempty f₁ hXne
  have hT_bddAbove : BddAbove T := hPr_bdd.image_eval 0 |>.bddAbove
  simpa [ubproj, S, T, hr] using csSup_le_csSup hT_bddAbove hS_nonempty hST

/--
Lemma 4.1 for the sliding-window relaxation with radius
`r = max (1, floor (α * L))`.
-/
theorem lemma41
    {d d' : Nat} (α : Real) (hα : α < 1)
    (f₁ : Net d d') (f₂ : Net d' 1) (s : Nat) (X : Set (Coord d))
    (hXne : X.Nonempty)
    (hlarge :
      let r := alphaRadius α (layerCount (pumpNetPr f₁ f₂ s))
      r ≤ s)
    (hglue :
      let r := alphaRadius α (layerCount (pumpNetPr f₁ f₂ s))
      let hr : 0 < r := alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s))
      let f₂' := prependIds (2 * (s - r)) f₂
      let left : LayerChain.T d d' :=
        LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r)
      let right : LayerChain.T d' 1 :=
        LayerChain.appendChain (LayerChain.idChain d' r) (LayerChain.FlattenNet f₂')
      let whole : LayerChain.T d 1 := LayerChain.appendChain left right
      ∀ {u : FullTrace left} {v : FullTrace right},
        u ∈ convHullTrace left X →
        v ∈ PrRelaxedSetChain r hr right {traceOutput u} →
        LayerChain.spliceTrace u v ∈ PrRelaxedSetChain r hr whole X)
    (hPr_bdd :
      Bornology.IsBounded
        (PrOutputSet
          (alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s)))
          (pumpNetPr f₁ f₂ s) X)) :
    lbproj 0 (reach f₂ (convexHull Real (reach f₁ X))) ≥
      lbproj 0
        (PrOutputSet
          (alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s)))
          (pumpNetPr f₁ f₂ s) X) ∧
    ubproj 0 (reach f₂ (convexHull Real (reach f₁ X))) ≤
      ubproj 0
        (PrOutputSet
          (alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s)))
          (pumpNetPr f₁ f₂ s) X) := by
  refine ⟨?_, ?_⟩
  · exact lemma41_lower α hα f₁ f₂ s X hXne hlarge hglue hPr_bdd
  · exact lemma41_upper α hα f₁ f₂ s X hXne hlarge hglue hPr_bdd

/--
Lower-bound half of Lemma 4.1 for the actual sliding-window `P_r` relaxation on
the pumped network with a `2r` identity buffer.
-/
theorem lemma41_fixedr_lower
    {d d' : Nat} (f₁ : Net d d') (f₂ : Net d' 1)
    (X : Polytope d) {r : Nat} (hr : 0 < r)
    (_h₁ : layerCount f₁ ≤ r) (_h₂ : layerCount f₂ ≤ r)
    (hXne : X.feasibleSet.Nonempty)
    (hglue : PumpGlueCondition hr f₁ f₂ X.feasibleSet)
    (hPr_bdd : Bornology.IsBounded (PrOutputSetOnPolytope hr (pumpNetPr f₁ f₂ r) X)) :
    lbPrActual hr (pumpNetPr f₁ f₂ r) X 0 ≤
      lbproj 0 (reach f₂ (convexHull Real (reach f₁ X.feasibleSet))) := by
  let S := proj 0 (reach f₂ (convexHull Real (reach f₁ X.feasibleSet)))
  let T := proj 0 (PrOutputSetOnPolytope hr (pumpNetPr f₁ f₂ r) X)
  have hbridge :
      reach f₂ (convexHull Real (reach f₁ X.feasibleSet)) ⊆
        PrOutputSetOnPolytope hr (pumpNetPr f₁ f₂ r) X := by
    exact reach_conv_middle_subset_PrOutputSet_pump hr f₁ f₂ X.feasibleSet hglue
  have hST : S ⊆ T := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact ⟨y, hbridge hy, rfl⟩
  have hS_nonempty : S.Nonempty := by
    apply proj_nonempty 0
    apply reach_nonempty
    apply convexHull_nonempty
    exact reach_nonempty f₁ hXne
  have hT_bddBelow : BddBelow T := hPr_bdd.image_eval 0 |>.bddBelow
  simpa [lbPrActual, S, T] using csInf_le_csInf hT_bddBelow hS_nonempty hST

/--
Upper-bound half of Lemma 4.1 for the actual sliding-window `P_r` relaxation on
the pumped network with a `2r` identity buffer.
-/
theorem lemma41_fixedr_upper
    {d d' : Nat} (f₁ : Net d d') (f₂ : Net d' 1)
    (X : Polytope d) {r : Nat} (hr : 0 < r)
    (_h₁ : layerCount f₁ ≤ r) (_h₂ : layerCount f₂ ≤ r)
    (hXne : X.feasibleSet.Nonempty)
    (hglue : PumpGlueCondition hr f₁ f₂ X.feasibleSet)
    (hPr_bdd : Bornology.IsBounded (PrOutputSetOnPolytope hr (pumpNetPr f₁ f₂ r) X)) :
    ubproj 0 (reach f₂ (convexHull Real (reach f₁ X.feasibleSet))) ≤
      ubPrActual hr (pumpNetPr f₁ f₂ r) X 0 := by
  let S := proj 0 (reach f₂ (convexHull Real (reach f₁ X.feasibleSet)))
  let T := proj 0 (PrOutputSetOnPolytope hr (pumpNetPr f₁ f₂ r) X)
  have hbridge :
      reach f₂ (convexHull Real (reach f₁ X.feasibleSet)) ⊆
        PrOutputSetOnPolytope hr (pumpNetPr f₁ f₂ r) X := by
    exact reach_conv_middle_subset_PrOutputSet_pump hr f₁ f₂ X.feasibleSet hglue
  have hST : S ⊆ T := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact ⟨y, hbridge hy, rfl⟩
  have hS_nonempty : S.Nonempty := by
    apply proj_nonempty 0
    apply reach_nonempty
    apply convexHull_nonempty
    exact reach_nonempty f₁ hXne
  have hT_bddAbove : BddAbove T := hPr_bdd.image_eval 0 |>.bddAbove
  simpa [ubPrActual, S, T] using csSup_le_csSup hT_bddAbove hS_nonempty hST

/--
Lemma 4.1 for the actual sliding-window `P_r` relaxation.

The pumped network is obtained by inserting `2r` identity layers between `f₁`
and `f₂`. The only remaining explicit hypotheses are the trace-gluing bridge
`hglue` and the boundedness of the pumped `P_r` output set.
-/
theorem lemma41_fixedr
    {d d' : Nat} (f₁ : Net d d') (f₂ : Net d' 1)
    (X : Polytope d) {r : Nat} (hr : 0 < r)
    (h₁ : layerCount f₁ ≤ r) (h₂ : layerCount f₂ ≤ r)
    (hXne : X.feasibleSet.Nonempty)
    (hglue : PumpGlueCondition hr f₁ f₂ X.feasibleSet)
    (hPr_bdd : Bornology.IsBounded (PrOutputSetOnPolytope hr (pumpNetPr f₁ f₂ r) X)) :
    reach (pumpNetPr f₁ f₂ r) X.feasibleSet = reach (Net.comp f₁ f₂) X.feasibleSet ∧
      lbPrActual hr (pumpNetPr f₁ f₂ r) X 0 ≤
        lbproj 0 (reach f₂ (convexHull Real (reach f₁ X.feasibleSet))) ∧
      ubproj 0 (reach f₂ (convexHull Real (reach f₁ X.feasibleSet))) ≤
        ubPrActual hr (pumpNetPr f₁ f₂ r) X 0 := by
  refine ⟨reach_pumpNetPr f₁ f₂ r X.feasibleSet,
    lemma41_fixedr_lower f₁ f₂ X hr h₁ h₂ hXne hglue hPr_bdd,
    lemma41_fixedr_upper f₁ f₂ X hr h₁ h₂ hXne hglue hPr_bdd⟩

end

end Net
