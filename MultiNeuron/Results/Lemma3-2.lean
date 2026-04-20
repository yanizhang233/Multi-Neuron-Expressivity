
import MultiNeuron.Relaxation.Layerwise
open Set

namespace Net

/-
This file formalizes Lemma 3.2 from the paper using the `P₁` definition from `LayerwisePolytope.lean`.
-/

/-- Project a set of vectors to the `o`-th coordinate. -/
def proj {m : Nat} (o : Fin m) (S : Set (Coord m)) : Set Real :=
  (fun y => y o) '' S

noncomputable def lbproj {m : Nat} (o : Fin m) (S : Set (Coord m)) : Real :=
  sInf (proj o S)

noncomputable def ubproj {m : Nat} (o : Fin m) (S : Set (Coord m)) : Real :=
  sSup (proj o S)

/-- Output lower bound returned by `P₁`, on coordinate `o`. -/
noncomputable def lbP1 {n m : Nat} (f : Net n m) (X : Polytope n) (o : Fin m) : Real :=
  lbproj o (P1OutputSetOnPolytope f X)

/-- Output upper bound returned by `P₁`, on coordinate `o`. -/
noncomputable def ubP1 {n m : Nat} (f : Net n m) (X : Polytope n) (o : Fin m) : Real :=
  ubproj o (P1OutputSetOnPolytope f X)

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

/--
Lower-bound half of Lemma 3.2.
-/
theorem lemma32Polytope_lower
    {n m k : Nat} (f₁ : Net n m) (f₂ : Net m k) (X : Polytope n) (o : Fin k)
    (hXne : X.feasibleSet.Nonempty) :
    lbP1 (Net.comp f₁ f₂) X o ≤
      lbproj o (reach f₂ (convexHull Real (reach f₁ X.feasibleSet))) := by
  let S := proj o (reach f₂ (convexHull Real (reach f₁ X.feasibleSet)))
  let T := proj o (P1OutputSetOnPolytope (Net.comp f₁ f₂) X)
  have hST : S ⊆ T := by
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    exact ⟨y, reach_comp_convex_subset_P1OutputSet_comp f₁ f₂ X.convex_feasibleSet hy, rfl⟩
  have hS_nonempty : S.Nonempty := by
    apply proj_nonempty o
    apply reach_nonempty
    apply convexHull_nonempty
    exact reach_nonempty f₁ hXne
  have hT_bddBelow : BddBelow T := ((P1OutputSetOnPolytope_bounded (Net.comp f₁ f₂) X).image_eval o).bddBelow
  simpa [lbP1, lbproj, S, T] using csInf_le_csInf hT_bddBelow hS_nonempty hST

/--
Upper-bound half of Lemma 3.2.
-/
theorem lemma32Polytope_upper
    {n m k : Nat} (f₁ : Net n m) (f₂ : Net m k) (X : Polytope n) (o : Fin k)
    (hXne : X.feasibleSet.Nonempty) :
    ubproj o (reach f₂ (convexHull Real (reach f₁ X.feasibleSet))) ≤
      ubP1 (Net.comp f₁ f₂) X o := by
  let S := proj o (reach f₂ (convexHull Real (reach f₁ X.feasibleSet)))
  let T := proj o (P1OutputSetOnPolytope (Net.comp f₁ f₂) X)
  have hST : S ⊆ T := by
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    exact ⟨y, reach_comp_convex_subset_P1OutputSet_comp f₁ f₂ X.convex_feasibleSet hy, rfl⟩
  have hS_nonempty : S.Nonempty := by
    apply proj_nonempty o
    apply reach_nonempty
    apply convexHull_nonempty
    exact reach_nonempty f₁ hXne
  have hT_bddAbove : BddAbove T := ((P1OutputSetOnPolytope_bounded (Net.comp f₁ f₂) X).image_eval o).bddAbove
  simpa [ubP1, ubproj, S, T] using csSup_le_csSup hT_bddAbove hS_nonempty hST

/-- Combined statement of Lemma 3.2. -/
theorem lemma32Polytope
    {n m k : Nat} (f₁ : Net n m) (f₂ : Net m k) (X : Polytope n) (o : Fin k)
    (hXne : X.feasibleSet.Nonempty) :
    lbP1 (Net.comp f₁ f₂) X o ≤
      lbproj o (reach f₂ (convexHull Real (reach f₁ X.feasibleSet))) ∧
    ubproj o (reach f₂ (convexHull Real (reach f₁ X.feasibleSet))) ≤
      ubP1 (Net.comp f₁ f₂) X o := by
  exact ⟨lemma32Polytope_lower f₁ f₂ X o hXne, lemma32Polytope_upper f₁ f₂ X o hXne⟩

end Net
