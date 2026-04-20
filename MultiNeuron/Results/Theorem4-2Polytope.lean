import MultiNeuron.Relaxation.CrosslayerPolytope
import MultiNeuron.Results.«Lemma3-2»
import MultiNeuron.Results.«Theorem3-3»

open Set

namespace Net

namespace Theorem42Polytope

noncomputable section

/-!
This file formalizes Theorem 4.2 for the cross-layer polytope relaxation.
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
The explicit block decomposition used in the pumped version of Theorem 4.2.
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
Choosing the pumping gap `⌈3 / γ⌉` guarantees that the resulting
`max(1, ⌈γ L⌉)` radius is at least `3`.
-/
theorem three_le_gammaRadius_pumpNet
    {d d' : Nat} (f₁ : Net d d') (f₂ : Net d' 1) {γ : Real}
    (hγ : 0 < γ) :
    3 ≤ gammaRadius γ (layerCount (pumpNet f₁ f₂ (Nat.ceil (3 / γ)))) := by
  let gap : Nat := Nat.ceil (3 / γ)
  have hgap_ge : (3 / γ : Real) ≤ gap := by
    exact (Nat.ceil_le).mp le_rfl
  have hdepth_nat : gap ≤ layerCount (pumpNet f₁ f₂ gap) := by
    have hbound : gap ≤ gap + (1 + (layerCount f₂ + layerCount f₁)) := by
      exact Nat.le_add_right _ _
    simpa [pumpNet, layerCount_prependIds, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound
  have hdepth_ge' : (gap : Real) ≤ layerCount (pumpNet f₁ f₂ gap) := by
    exact_mod_cast hdepth_nat
  have hthree_le_gap : (3 : Real) ≤ γ * gap := by
    have hmul : γ * (3 / γ) ≤ γ * gap := by
      exact mul_le_mul_of_nonneg_left hgap_ge (le_of_lt hγ)
    have hγne : γ ≠ 0 := ne_of_gt hγ
    have hthree : γ * (3 / γ) = 3 := by
      field_simp [hγne]
    simpa [hthree] using hmul
  have hgap_mul_depth : γ * gap ≤ γ * layerCount (pumpNet f₁ f₂ gap) := by
    exact mul_le_mul_of_nonneg_left hdepth_ge' (le_of_lt hγ)
  have hthree_le_depth : (3 : Real) ≤ γ * layerCount (pumpNet f₁ f₂ gap) :=
    le_trans hthree_le_gap hgap_mul_depth
  have hceil : γ * layerCount (pumpNet f₁ f₂ gap) ≤
      (Nat.ceil (γ * layerCount (pumpNet f₁ f₂ gap)) : Real) := by
    exact (Nat.ceil_le).mp le_rfl
  have hthree_nat : 3 ≤ Nat.ceil (γ * layerCount (pumpNet f₁ f₂ gap)) := by
    exact Nat.cast_le.mp (by exact le_trans hthree_le_depth hceil)
  exact le_trans hthree_nat (Nat.le_max_right _ _)

theorem theorem42Polytope_lower
    {d : Nat} (X : Polytope (Nat.succ d)) {a b γ T : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hab : a < b) (hγ : 0 < γ) (_hγ' : γ < 1) (hT : 0 < T) :
    ∃ f : Net (Nat.succ d) 1,
      ∃ D : BlockDecomposition (gammaRadius γ (layerCount f)) (Nat.succ d) 1,
        BlockDecomposition.toNet D = f ∧
        lbPr D X 0 ≤ lbproj 0 (reach f X.feasibleSet) - T := by
  let gap : Nat := Nat.ceil (3 / γ)
  let f : Net (Nat.succ d) 1 :=
    pumpNet (prefixNet (d := d) a b) (valleyNet T) gap
  have hr : 3 ≤ gammaRadius γ (layerCount f) := by
    simpa [f, gap] using
      (three_le_gammaRadius_pumpNet (prefixNet (d := d) a b) (valleyNet T) hγ)
  have hprefix : layerCount (prefixNet (d := d) a b) ≤ gammaRadius γ (layerCount f) := by
    simpa [prefixNet, normalize1DNet, liftNet, f, gap] using hr
  have hvalley : layerCount (valleyNet T) ≤ gammaRadius γ (layerCount f) := by
    simpa [valleyNet, absNet, sumNet, f, gap] using hr
  let D : BlockDecomposition (gammaRadius γ (layerCount f)) (Nat.succ d) 1 :=
    pumpDecomposition (prefixNet (d := d) a b) hprefix (valleyNet T) hvalley gap
  refine ⟨f, D, ?_, ?_⟩
  · simp [D, f, gap, pumpDecomposition, pumpNet]
  let exactSet := proj 0 (reach f X.feasibleSet)
  have hXne : X.feasibleSet.Nonempty := by
    rcases Theorem33Polytope.exists_mem_of_firstCoord hproj
      (by exact ⟨le_rfl, le_of_lt hab⟩) with ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  have hexact_nonempty : exactSet.Nonempty := by
    apply proj_nonempty 0
    exact reach_nonempty f hXne
  have hExact_ge : ∀ r ∈ exactSet, T ≤ r := by
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    have hy' : y ∈ reach (lowerCounterexample (d := d) a b T) X.feasibleSet := by
      simpa [exactSet, f, gap, lowerCounterexample] using hy
    rcases hy' with ⟨x, hxX, rfl⟩
    have hx0 : x 0 ∈ Set.Icc a b := Theorem33Polytope.firstCoord_mem_Icc hproj hxX
    have hnorm : normalized a b (x 0) ∈ Set.Icc (-1 : Real) 1 :=
      normalized_mem_Icc hab hx0
    simpa [lowerCounterexample, eval_valleyNet, eval_prefixNet] using
      Theorem33Polytope.valleyValue_prefix_ge T (normalized a b (x 0)) hT hnorm
  have hmin_ge : T ≤ lbproj 0 (reach f X.feasibleSet) := by
    simpa [lbproj, exactSet] using le_csInf hexact_nonempty hExact_ge
  have hlemma :
      lbPr D X 0 ≤
        lbproj 0 (reach (valleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by
    simpa [D] using lemma41Polytope_lower (prefixNet (d := d) a b) (valleyNet T) X hprefix hvalley gap hXne
  have hreach_mid : (![(0 : Real)] : Coord 1) ∈
      reach (valleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)) := by
    refine ⟨midPoint, Theorem33Polytope.midPoint_mem_convexHull_reach_prefix hproj hab, ?_⟩
    ext i
    fin_cases i
    simp [eval_valleyNet, valleyValue_at_midPoint]
  have hzero_mem : (0 : Real) ∈
      proj 0 (reach (valleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by
    exact ⟨![0], hreach_mid, rfl⟩
  have hconv_bddBelow : BddBelow
      (proj 0 (reach (valleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)))) := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    exact Theorem33Polytope.exact_valley_nonneg T (le_of_lt hT) z
  have hlb_le_zero :
      lbproj 0 (reach (valleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) ≤ 0 := by
    simpa [lbproj, proj] using csInf_le hconv_bddBelow hzero_mem
  have hlbPr_le_zero : lbPr D X 0 ≤ 0 := le_trans hlemma hlb_le_zero
  linarith

theorem theorem42Polytope_upper
    {d : Nat} (X : Polytope (Nat.succ d)) {a b γ T : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hab : a < b) (hγ : 0 < γ) (_hγ' : γ < 1) (hT : 0 < T) :
    ∃ g : Net (Nat.succ d) 1,
      ∃ D : BlockDecomposition (gammaRadius γ (layerCount g)) (Nat.succ d) 1,
        BlockDecomposition.toNet D = g ∧
        ubproj 0 (reach g X.feasibleSet) + T ≤ ubPr D X 0 := by
  let gap : Nat := Nat.ceil (3 / γ)
  let g : Net (Nat.succ d) 1 :=
    pumpNet (prefixNet (d := d) a b) (negValleyNet T) gap
  have hr : 3 ≤ gammaRadius γ (layerCount g) := by
    simpa [g, gap] using
      (three_le_gammaRadius_pumpNet (prefixNet (d := d) a b) (negValleyNet T) hγ)
  have hprefix : layerCount (prefixNet (d := d) a b) ≤ gammaRadius γ (layerCount g) := by
    simpa [prefixNet, normalize1DNet, liftNet, g, gap] using hr
  have hnegValley : layerCount (negValleyNet T) ≤ gammaRadius γ (layerCount g) := by
    simpa [negValleyNet, absNet, sumNet, g, gap] using hr
  let D : BlockDecomposition (gammaRadius γ (layerCount g)) (Nat.succ d) 1 :=
    pumpDecomposition (prefixNet (d := d) a b) hprefix (negValleyNet T) hnegValley gap
  refine ⟨g, D, ?_, ?_⟩
  · simp [D, g, gap, pumpDecomposition, pumpNet]
  let exactSet := proj 0 (reach g X.feasibleSet)
  have hXne : X.feasibleSet.Nonempty := by
    rcases Theorem33Polytope.exists_mem_of_firstCoord hproj
      (by exact ⟨le_rfl, le_of_lt hab⟩) with ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  have hexact_nonempty : exactSet.Nonempty := by
    apply proj_nonempty 0
    exact reach_nonempty g hXne
  have hExact_le : ∀ r ∈ exactSet, r ≤ -T := by
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    have hy' : y ∈ reach (upperCounterexample (d := d) a b T) X.feasibleSet := by
      simpa [exactSet, g, gap, upperCounterexample] using hy
    rcases hy' with ⟨x, hxX, rfl⟩
    have hx0 : x 0 ∈ Set.Icc a b := Theorem33Polytope.firstCoord_mem_Icc hproj hxX
    have hnorm : normalized a b (x 0) ∈ Set.Icc (-1 : Real) 1 :=
      normalized_mem_Icc hab hx0
    have hge : T ≤ valleyValue T (prefixPoint (normalized a b (x 0))) :=
      Theorem33Polytope.valleyValue_prefix_ge T (normalized a b (x 0)) hT hnorm
    have hneg : -valleyValue T (prefixPoint (normalized a b (x 0))) ≤ -T := by
      linarith
    simpa [upperCounterexample, eval_negValleyNet, eval_prefixNet] using hneg
  have hmax_le : ubproj 0 (reach g X.feasibleSet) ≤ -T := by
    simpa [ubproj, exactSet] using csSup_le hexact_nonempty hExact_le
  have hlemma :
      ubproj 0 (reach (negValleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) ≤
        ubPr D X 0 := by
    simpa [D] using lemma41Polytope_upper (prefixNet (d := d) a b) (negValleyNet T) X hprefix hnegValley gap hXne
  have hreach_mid : (![(0 : Real)] : Coord 1) ∈
      reach (negValleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)) := by
    refine ⟨midPoint, Theorem33Polytope.midPoint_mem_convexHull_reach_prefix hproj hab, ?_⟩
    ext i
    fin_cases i
    simp [eval_negValleyNet, valleyValue_at_midPoint]
  have hzero_mem : (0 : Real) ∈
      proj 0 (reach (negValleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by
    exact ⟨![0], hreach_mid, rfl⟩
  have hconv_bddAbove : BddAbove
      (proj 0 (reach (negValleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)))) := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    exact Theorem33Polytope.exact_negValley_nonpos T (le_of_lt hT) z
  have hzero_le_ub :
      0 ≤ ubproj 0 (reach (negValleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by
    simpa [ubproj, proj] using le_csSup hconv_bddAbove hzero_mem
  have hzero_le_ubPr : 0 ≤ ubPr D X 0 := le_trans hzero_le_ub hlemma
  linarith

/-- Polytope version of Theorem 4.2. -/
theorem theorem42Polytope
    {d : Nat} (X : Polytope (Nat.succ d)) {a b γ T : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hab : a < b) (hγ : 0 < γ) (hγ' : γ < 1) (hT : 0 < T) :
    (∃ f : Net (Nat.succ d) 1,
        ∃ D : BlockDecomposition (gammaRadius γ (layerCount f)) (Nat.succ d) 1,
          BlockDecomposition.toNet D = f ∧
          lbPr D X 0 ≤ lbproj 0 (reach f X.feasibleSet) - T) ∧
      (∃ g : Net (Nat.succ d) 1,
        ∃ D : BlockDecomposition (gammaRadius γ (layerCount g)) (Nat.succ d) 1,
          BlockDecomposition.toNet D = g ∧
          ubproj 0 (reach g X.feasibleSet) + T ≤ ubPr D X 0) := by
  refine ⟨theorem42Polytope_lower X hproj hab hγ hγ' hT,
    theorem42Polytope_upper X hproj hab hγ hγ' hT⟩

end

end Theorem42Polytope

end Net
