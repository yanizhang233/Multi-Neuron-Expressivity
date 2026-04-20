import MultiNeuron.Relaxation.Crosslayer
import MultiNeuron.Results.«Lemma3-2»

open Set

namespace Net

noncomputable section

/-!
This file formalizes a polytope version of Lemma 4.1 using the cross-layer
polytope backend.
-/

/-- `repeatId n k` is a chain of `k + 1` dummy identity layers on `Coord n`. -/
def repeatId (n : Nat) : Nat → Net n n
  | 0 => Net.idLayer n
  | k + 1 => Net.comp (Net.idLayer n) (repeatId n k)

@[simp] theorem layerCount_repeatId (n : Nat) : ∀ k, layerCount (repeatId n k) = k + 1
  | 0 => by simp [repeatId]
  | k + 1 => by
      simp [repeatId, layerCount_repeatId n k, Nat.add_left_comm, Nat.add_comm]

@[simp] theorem eval_repeatId (n : Nat) : ∀ k, eval (repeatId n k) = _root_.id
  | 0 => rfl
  | k + 1 => by
      funext x
      simp [repeatId, eval_repeatId n k, Net.eval]

@[simp] theorem reach_repeatId (n : Nat) (k : Nat) (X : Set (Coord n)) :
    reach (repeatId n k) X = X := by
  simp [Net.reach, eval_repeatId]

/-- The depth-dependent radius `max(1, ⌈γ L⌉)`. -/
noncomputable def gammaRadius (γ : Real) (L : Nat) : Nat :=
  max 1 (Nat.ceil (γ * L))

/-- Lower bound returned by a cross-layer relaxation on a polytope input. -/
noncomputable def lbPr {r n m : Nat}
    (D : BlockDecomposition r n m) (X : Polytope n) (o : Fin m) : Real :=
  lbproj o (PrOutputSetOfDecomposition D X.feasibleSet)

/-- Upper bound returned by a cross-layer relaxation on a polytope input. -/
noncomputable def ubPr {r n m : Nat}
    (D : BlockDecomposition r n m) (X : Polytope n) (o : Fin m) : Real :=
  ubproj o (PrOutputSetOfDecomposition D X.feasibleSet)

/-- Append two block decompositions. -/
def appendDecomposition {r n m k : Nat} :
    BlockDecomposition r n m → BlockDecomposition r m k → BlockDecomposition r n k
  | .single f hcount, tail => .comp f hcount tail
  | .comp f hcount rest, tail => .comp f hcount (appendDecomposition rest tail)

/-- Prepend `gap + 1` identity layers in front of a network. -/
def prependIds {n m : Nat} (f : Net n m) : Nat → Net n m
  | 0 => Net.comp (Net.idLayer n) f
  | k + 1 => Net.comp (Net.idLayer n) (prependIds f k)

@[simp] theorem layerCount_prependIds {n m : Nat} (f : Net n m) :
    ∀ gap, layerCount (prependIds f gap) = gap + 1 + layerCount f
  | 0 => by simp [prependIds]
  | gap + 1 => by
      simp [prependIds, layerCount_prependIds f gap, Nat.add_left_comm, Nat.add_comm]

@[simp] theorem eval_prependIds {n m : Nat} (f : Net n m) :
    ∀ gap, eval (prependIds f gap) = eval f
  | 0 => by
      funext x
      simp [prependIds, Net.eval]
  | gap + 1 => by
      funext x
      simp [prependIds, eval_prependIds f gap, Net.eval]

/-- Decompose `repeatId n k` into single-identity blocks. -/
def repeatIdDecomposition (n r : Nat) (hr : 1 ≤ r) : Nat → BlockDecomposition r n n
  | 0 => .single (Net.idLayer n) (by simpa [layerCount] using hr)
  | k + 1 => .comp (Net.idLayer n) (by simpa [layerCount] using hr) (repeatIdDecomposition n r hr k)

@[simp] theorem repeatIdDecomposition_toNet (n r : Nat) (hr : 1 ≤ r) :
    ∀ k, BlockDecomposition.toNet (repeatIdDecomposition n r hr k) = repeatId n k
  | 0 => by
      simp [repeatIdDecomposition, repeatId]
  | k + 1 => by
      simp [repeatIdDecomposition, repeatId, repeatIdDecomposition_toNet n r hr k]

@[simp] theorem blockRelax_idLayer (n : Nat) (X : Set (Coord n)) :
    blockRelax (Net.idLayer n) X = convexHull Real X := by
  rw [blockRelax_eq_convexHull_reach, Net.reach]
  simp

@[simp] theorem PrOutputSetOfDecomposition_appendDecomposition {r n m k : Nat}
    (D₁ : BlockDecomposition r n m) (D₂ : BlockDecomposition r m k) (X : Set (Coord n)) :
    PrOutputSetOfDecomposition (appendDecomposition D₁ D₂) X =
      PrOutputSetOfDecomposition D₂ (PrOutputSetOfDecomposition D₁ X) := by
  induction D₁ with
  | single f hcount =>
      rw [appendDecomposition, PrOutputSetOfDecomposition_comp, PrOutputSetOfDecomposition_single]
  | comp f hcount rest ih =>
      rw [appendDecomposition, PrOutputSetOfDecomposition_comp, ih, PrOutputSetOfDecomposition_comp]

@[simp] theorem PrOutputSetOfDecomposition_repeatIdDecomposition (n r : Nat) (hr : 1 ≤ r) :
    ∀ gap (X : Set (Coord n)),
      PrOutputSetOfDecomposition (repeatIdDecomposition n r hr gap) X = convexHull Real X
  | 0, X => by
      rw [repeatIdDecomposition, PrOutputSetOfDecomposition_single, blockRelax_idLayer]
  | gap + 1, X => by
      rw [repeatIdDecomposition, PrOutputSetOfDecomposition_comp,
        PrOutputSetOfDecomposition_repeatIdDecomposition n r hr gap]
      rw [blockRelax_idLayer]
      exact (convex_convexHull Real X).convexHull_eq

/-- Pump a composition by inserting a chain of dummy identity layers in the middle. -/
def pumpNet {d d' : Nat} (f₁ : Net d d') (f₂ : Net d' 1) (gap : Nat) : Net d 1 :=
  Net.comp f₁ (prependIds f₂ gap)

/--
The explicit block decomposition used in the pumped version of Lemma 4.1:
one block for `f₁`, then the dummy identities split into single-identity
blocks, and finally one block for `f₂`.
-/
def pumpDecomposition {r d d' : Nat}
    (f₁ : Net d d') (h₁ : layerCount f₁ ≤ r)
    (f₂ : Net d' 1) (h₂ : layerCount f₂ ≤ r) (gap : Nat) :
    BlockDecomposition r d 1 :=
  let hr : 1 ≤ r := le_trans (one_le_layerCount f₂) h₂
  .comp f₁ h₁ (appendDecomposition (repeatIdDecomposition d' r hr gap) (.single f₂ h₂))

@[simp] theorem append_repeatIdDecomposition_single_toNet
    {r n m : Nat} (hr : 1 ≤ r) (f : Net n m) (hcount : layerCount f ≤ r) :
    ∀ gap,
      BlockDecomposition.toNet
          (appendDecomposition (repeatIdDecomposition n r hr gap) (.single f hcount)) =
        prependIds f gap
  | 0 => by
      simp [appendDecomposition, repeatIdDecomposition, prependIds]
  | gap + 1 => by
      simp [appendDecomposition, repeatIdDecomposition, prependIds,
        append_repeatIdDecomposition_single_toNet hr f hcount gap]

@[simp] theorem pumpDecomposition_toNet {r d d' : Nat}
    (f₁ : Net d d') (h₁ : layerCount f₁ ≤ r)
    (f₂ : Net d' 1) (h₂ : layerCount f₂ ≤ r) (gap : Nat) :
    BlockDecomposition.toNet (pumpDecomposition f₁ h₁ f₂ h₂ gap) = pumpNet f₁ f₂ gap := by
  let hr : 1 ≤ r := le_trans (one_le_layerCount f₂) h₂
  simp [pumpDecomposition, pumpNet, append_repeatIdDecomposition_single_toNet]

@[simp] theorem eval_pumpNet {d d' : Nat} (f₁ : Net d d') (f₂ : Net d' 1) (gap : Nat) :
    eval (pumpNet f₁ f₂ gap) = eval (Net.comp f₁ f₂) := by
  funext x
  simp [pumpNet, eval_prependIds, Net.eval]

@[simp] theorem reach_pumpNet {d d' : Nat}
    (f₁ : Net d d') (f₂ : Net d' 1) (gap : Nat) (X : Set (Coord d)) :
    reach (pumpNet f₁ f₂ gap) X = reach (Net.comp f₁ f₂) X := by
  simp [Net.reach, eval_pumpNet]

@[simp] theorem blockRelax_repeatId {n : Nat} (gap : Nat) (X : Set (Coord n)) :
    blockRelax (repeatId n gap) X = convexHull Real X := by
  simp [blockRelax_eq_convexHull_reach, reach_repeatId]

theorem blockRelax_repeatId_of_convex {n : Nat} (gap : Nat) {X : Set (Coord n)}
    (hX : Convex Real X) :
    blockRelax (repeatId n gap) X = X := by
  rw [blockRelax_repeatId]
  simpa using hX.convexHull_eq

@[simp] theorem PrOutputSet_pumpDecomposition {r d d' : Nat}
    (f₁ : Net d d') (h₁ : layerCount f₁ ≤ r)
    (f₂ : Net d' 1) (h₂ : layerCount f₂ ≤ r)
    (gap : Nat) (X : Set (Coord d)) :
    PrOutputSetOfDecomposition (pumpDecomposition f₁ h₁ f₂ h₂ gap) X =
      blockRelax f₂ (blockRelax f₁ X) := by
  have hr : 1 ≤ r := le_trans (one_le_layerCount f₂) h₂
  rw [pumpDecomposition, PrOutputSetOfDecomposition_comp,
    PrOutputSetOfDecomposition_appendDecomposition,
    PrOutputSetOfDecomposition_repeatIdDecomposition]
  rw [PrOutputSetOfDecomposition_single]
  have hconv : Convex Real (blockRelax f₁ X) := blockRelax_convex f₁ X
  rw [hconv.convexHull_eq]

/--
The pumped decomposition computes exactly the convex hull of the suffix image on
the convexified prefix reach set.
-/
theorem PrOutputSet_pumpDecomposition_eq {r d d' : Nat}
    (f₁ : Net d d') (h₁ : layerCount f₁ ≤ r)
    (f₂ : Net d' 1) (h₂ : layerCount f₂ ≤ r)
    (gap : Nat) (X : Set (Coord d)) :
    PrOutputSetOfDecomposition (pumpDecomposition f₁ h₁ f₂ h₂ gap) X =
      convexHull Real (reach f₂ (convexHull Real (reach f₁ X))) := by
  rw [PrOutputSet_pumpDecomposition]
  rw [blockRelax_eq_convexHull_reach, blockRelax_eq_convexHull_reach]

@[simp] theorem PrOutputSetOnPolytope_pumpDecomposition_eq {r d d' : Nat}
    (f₁ : Net d d') (h₁ : layerCount f₁ ≤ r)
    (f₂ : Net d' 1) (h₂ : layerCount f₂ ≤ r)
    (gap : Nat) (X : Polytope d) :
    PrOutputSetOfDecomposition (pumpDecomposition f₁ h₁ f₂ h₂ gap) X.feasibleSet =
      convexHull Real (reach f₂ (convexHull Real (reach f₁ X.feasibleSet))) := by
  exact PrOutputSet_pumpDecomposition_eq f₁ h₁ f₂ h₂ gap X.feasibleSet

/--
Lower-bound half of the pumped cross-layer version of Lemma 4.1.
-/
theorem lemma41Polytope_lower
    {d d' : Nat} (f₁ : Net d d') (f₂ : Net d' 1)
    (X : Polytope d) {r : Nat}
    (h₁ : layerCount f₁ ≤ r) (h₂ : layerCount f₂ ≤ r)
    (gap : Nat) (hXne : X.feasibleSet.Nonempty) :
    lbPr (pumpDecomposition f₁ h₁ f₂ h₂ gap) X 0 ≤
      lbproj 0 (reach f₂ (convexHull Real (reach f₁ X.feasibleSet))) := by
  let D : BlockDecomposition r d 1 := pumpDecomposition f₁ h₁ f₂ h₂ gap
  let S := proj 0 (reach f₂ (convexHull Real (reach f₁ X.feasibleSet)))
  let T := proj 0 (PrOutputSetOfDecomposition D X.feasibleSet)
  have hST : S ⊆ T := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    refine ⟨y, ?_, rfl⟩
    change y ∈ PrOutputSetOfDecomposition (pumpDecomposition f₁ h₁ f₂ h₂ gap) X.feasibleSet
    rw [PrOutputSetOnPolytope_pumpDecomposition_eq]
    exact subset_convexHull Real _ hy
  have hS_nonempty : S.Nonempty := by
    apply proj_nonempty 0
    apply reach_nonempty
    apply convexHull_nonempty
    exact reach_nonempty f₁ hXne
  have hT_bddBelow : BddBelow T :=
    (PrOutputSetOfDecomposition_bounded D X.isBounded_feasibleSet).image_eval 0 |>.bddBelow
  simpa [lbPr, D, S, T] using csInf_le_csInf hT_bddBelow hS_nonempty hST

/--
Upper-bound half of the pumped cross-layer version of Lemma 4.1.
-/
theorem lemma41Polytope_upper
    {d d' : Nat} (f₁ : Net d d') (f₂ : Net d' 1)
    (X : Polytope d) {r : Nat}
    (h₁ : layerCount f₁ ≤ r) (h₂ : layerCount f₂ ≤ r)
    (gap : Nat) (hXne : X.feasibleSet.Nonempty) :
    ubproj 0 (reach f₂ (convexHull Real (reach f₁ X.feasibleSet))) ≤
      ubPr (pumpDecomposition f₁ h₁ f₂ h₂ gap) X 0 := by
  let D : BlockDecomposition r d 1 := pumpDecomposition f₁ h₁ f₂ h₂ gap
  let S := proj 0 (reach f₂ (convexHull Real (reach f₁ X.feasibleSet)))
  let T := proj 0 (PrOutputSetOfDecomposition D X.feasibleSet)
  have hST : S ⊆ T := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    refine ⟨y, ?_, rfl⟩
    change y ∈ PrOutputSetOfDecomposition (pumpDecomposition f₁ h₁ f₂ h₂ gap) X.feasibleSet
    rw [PrOutputSetOnPolytope_pumpDecomposition_eq]
    exact subset_convexHull Real _ hy
  have hS_nonempty : S.Nonempty := by
    apply proj_nonempty 0
    apply reach_nonempty
    apply convexHull_nonempty
    exact reach_nonempty f₁ hXne
  have hT_bddAbove : BddAbove T :=
    (PrOutputSetOfDecomposition_bounded D X.isBounded_feasibleSet).image_eval 0 |>.bddAbove
  simpa [ubPr, D, S, T] using csSup_le_csSup hT_bddAbove hS_nonempty hST

/--
Combined polytope version of Lemma 4.1 for the explicit-decomposition
cross-layer relaxation.
-/
theorem lemma41Polytope
    {d d' : Nat} (f₁ : Net d d') (f₂ : Net d' 1)
    (X : Polytope d) {r : Nat}
    (h₁ : layerCount f₁ ≤ r) (h₂ : layerCount f₂ ≤ r)
    (gap : Nat) (hXne : X.feasibleSet.Nonempty) :
    reach (pumpNet f₁ f₂ gap) X.feasibleSet = reach (Net.comp f₁ f₂) X.feasibleSet ∧
      lbPr (pumpDecomposition f₁ h₁ f₂ h₂ gap) X 0 ≤
        lbproj 0 (reach f₂ (convexHull Real (reach f₁ X.feasibleSet))) ∧
      ubproj 0 (reach f₂ (convexHull Real (reach f₁ X.feasibleSet))) ≤
        ubPr (pumpDecomposition f₁ h₁ f₂ h₂ gap) X 0 := by
  refine ⟨reach_pumpNet f₁ f₂ gap X.feasibleSet,
    lemma41Polytope_lower f₁ f₂ X h₁ h₂ gap hXne,
    lemma41Polytope_upper f₁ f₂ X h₁ h₂ gap hXne⟩

end

end Net
