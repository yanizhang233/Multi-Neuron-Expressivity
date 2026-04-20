import MultiNeuron.Results.«Lemma4-1»
import MultiNeuron.Results.«Theorem3-3»

open Set

namespace MultiNeuron

namespace Net

namespace Theorem42

noncomputable section

/-!
This file formalizes Theorem 4.2 for the current explicit-decomposition
cross-layer relaxation.

As in `Theorem3-3.lean`, we work with the same semantic substitute for a convex
polytope: a convex input set whose first-coordinate projection is a nontrivial
interval.
-/

/-- The midpoint witness already lies in the convex hull of the exact prefix reach set. -/
theorem midPoint_mem_convexHull_reach_prefix
    {d : Nat} {X : Set (Coord (Nat.succ d))} {a b : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X = Set.Icc a b) (hab : a < b) :
    midPoint ∈ convexHull Real (reach (prefixNet (d := d) a b) X) := by
  have hleft : leftPoint ∈ reach (prefixNet (d := d) a b) X :=
    Theorem33.leftPoint_in_reach_prefix hproj hab
  have hright : rightPoint ∈ reach (prefixNet (d := d) a b) X :=
    Theorem33.rightPoint_in_reach_prefix hproj hab
  have hmid' : (1 / 2 : Real) • leftPoint + (1 / 2 : Real) • rightPoint ∈
      convexHull Real (reach (prefixNet (d := d) a b) X) := by
    apply (convex_convexHull Real _)
      (subset_convexHull Real _ hleft)
      (subset_convexHull Real _ hright) <;> norm_num
  simpa [leftPoint, rightPoint, midPoint] using hmid'

/--
Choosing the pumping gap `⌈3 / γ⌉` guarantees that the resulting
`max(1, ⌈γ L⌉)` radius is at least `3`.
-/
theorem three_le_gammaRadius_pumpNet
    {d d' : Nat} (f₁ : Net d d') (f₂ : Net d' 1) {γ : Real}
    (hγ : 0 < γ) :
    3 ≤ gammaRadius γ (syntacticDepth (pumpNet f₁ f₂ (Nat.ceil (3 / γ)))) := by
  let gap : Nat := Nat.ceil (3 / γ)
  have hgap_ge : (3 / γ : Real) ≤ gap := by
    exact (Nat.ceil_le).mp le_rfl
  have hdepth_nat : gap ≤ syntacticDepth (pumpNet f₁ f₂ gap) := by
    have : gap ≤ gap + (syntacticDepth f₁ + (1 + syntacticDepth f₂)) :=
      Nat.le_add_right gap (syntacticDepth f₁ + (1 + syntacticDepth f₂))
    simpa [pumpNet, syntacticDepth_repeatId, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      this
  have hdepth_ge' : (gap : Real) ≤ syntacticDepth (pumpNet f₁ f₂ gap) := by
    exact_mod_cast hdepth_nat
  have hthree_le_gap : (3 : Real) ≤ γ * gap := by
    have hmul : γ * (3 / γ) ≤ γ * gap := by
      exact mul_le_mul_of_nonneg_left hgap_ge (le_of_lt hγ)
    have hγne : γ ≠ 0 := ne_of_gt hγ
    have hthree : γ * (3 / γ) = 3 := by
      field_simp [hγne]
    simpa [hthree] using hmul
  have hgap_mul_depth : γ * gap ≤ γ * syntacticDepth (pumpNet f₁ f₂ gap) := by
    exact mul_le_mul_of_nonneg_left hdepth_ge' (le_of_lt hγ)
  have hthree_le_depth : (3 : Real) ≤ γ * syntacticDepth (pumpNet f₁ f₂ gap) :=
    le_trans hthree_le_gap hgap_mul_depth
  have hceil : γ * syntacticDepth (pumpNet f₁ f₂ gap) ≤
      (Nat.ceil (γ * syntacticDepth (pumpNet f₁ f₂ gap)) : Real) := by
    exact (Nat.ceil_le).mp le_rfl
  have hthree_nat : 3 ≤ Nat.ceil (γ * syntacticDepth (pumpNet f₁ f₂ gap)) := by
    exact Nat.cast_le.mp (by exact le_trans hthree_le_depth hceil)
  exact le_trans hthree_nat (Nat.le_max_right _ _)

theorem theorem42_lower
    {d : Nat} {X : Set (Coord (Nat.succ d))} {a b γ T : Real}
    (_hXconv : Convex Real X)
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X = Set.Icc a b)
    (hab : a < b) (hγ : 0 < γ) (_hγ' : γ < 1) (hT : 0 < T) :
    ∃ f : Net (Nat.succ d) 1,
      ∃ D : BlockDecomposition (gammaRadius γ (syntacticDepth f)) (Nat.succ d) 1,
        BlockDecomposition.toNet D = f ∧
        lbPr D X 0 ≤ sInf (coordImage 0 (reach f X)) - T := by
  let gap : Nat := Nat.ceil (3 / γ)
  let f : Net (Nat.succ d) 1 :=
    pumpNet (prefixNet (d := d) a b) (valleyNet T) gap
  have hr : 3 ≤ gammaRadius γ (syntacticDepth f) := by
    simpa [f, gap] using
      (three_le_gammaRadius_pumpNet (prefixNet (d := d) a b) (valleyNet T) hγ)
  have hprefix : layerCount (prefixNet (d := d) a b) ≤ gammaRadius γ (syntacticDepth f) := by
    simpa [prefixNet, normalizeNet, liftNet, f, gap] using hr
  have hvalley : layerCount (valleyNet T) ≤ gammaRadius γ (syntacticDepth f) := by
    simpa [valleyNet, diffNet, sumNet, f, gap] using hr
  let D : BlockDecomposition (gammaRadius γ (syntacticDepth f)) (Nat.succ d) 1 :=
    pumpDecomposition (prefixNet (d := d) a b) hprefix (valleyNet T) hvalley gap
  refine ⟨f, D, ?_, ?_⟩
  · simp [D, f, gap, pumpDecomposition, pumpNet]
  let exactSet := coordImage 0 (reach f X)
  let relaxSet := coordImage 0 (PrRelax D X)
  have hXne : X.Nonempty := by
    rcases Theorem33.exists_mem_of_firstCoord hproj (by exact ⟨le_rfl, le_of_lt hab⟩) with
      ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  have hexact_nonempty : exactSet.Nonempty := by
    apply coordImage_nonempty 0
    exact reach_nonempty f hXne
  have hExact_ge : ∀ r ∈ exactSet, T ≤ r := by
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    have hy' : y ∈ reach (lowerCounterexample (d := d) a b T) X := by
      simpa [exactSet, D, f, gap, lowerCounterexample] using hy
    rcases hy' with ⟨x, hxX, rfl⟩
    have hx0 : x 0 ∈ Set.Icc a b := Theorem33.firstCoord_mem_Icc hproj hxX
    have hnorm : normalized a b (x 0) ∈ Set.Icc (-1 : Real) 1 :=
      normalized_mem_Icc hab hx0
    simpa [lowerCounterexample, eval_valleyNet, eval_prefixNet] using
      valleyValue_prefix_ge T (normalized a b (x 0)) hT hnorm
  have hmin_ge : T ≤ sInf exactSet := le_csInf hexact_nonempty hExact_ge
  have hmid : midPoint ∈ convexHull Real (reach (prefixNet (d := d) a b) X) :=
    midPoint_mem_convexHull_reach_prefix hproj hab
  have hzero_mem : (0 : Real) ∈ relaxSet := by
    have hreach_mid : (((fun _ : Fin 1 => (0 : Real)) : Coord 1)) ∈
        reach (valleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X)) := by
      refine ⟨midPoint, hmid, ?_⟩
      ext i
      fin_cases i
      simp [eval_valleyNet, valleyValue_at_midPoint]
    have hrel_mid : (((fun _ : Fin 1 => (0 : Real)) : Coord 1)) ∈ PrRelax D X := by
      rw [PrRelax_pumpDecomposition_eq]
      exact subset_convexHull Real _ hreach_mid
    exact ⟨((fun _ : Fin 1 => (0 : Real)) : Coord 1), hrel_mid, rfl⟩
  let K : Set (Coord 1) := {y | 0 ≤ y 0}
  have hK_conv : Convex Real K := by
    intro y hy z hz α β hα hβ hαβ
    dsimp [K] at hy hz ⊢
    nlinarith
  have hreach_nonneg :
      reach (valleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X)) ⊆ K := by
    intro y hy
    rcases hy with ⟨z, -, rfl⟩
    dsimp [K]
    simpa [eval_valleyNet] using valleyValue_nonneg T (le_of_lt hT) z
  have hrel_bddBelow : BddBelow relaxSet := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    have hyK : y ∈ K := by
      rw [PrRelax_pumpDecomposition_eq] at hy
      exact convexHull_min hreach_nonneg hK_conv hy
    simpa [K] using hyK
  have hlb_le_zero : lbPr D X 0 ≤ 0 := by
    simpa [lbPr, relaxSet] using csInf_le hrel_bddBelow hzero_mem
  linarith

theorem theorem42_upper
    {d : Nat} {X : Set (Coord (Nat.succ d))} {a b γ T : Real}
    (_hXconv : Convex Real X)
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X = Set.Icc a b)
    (hab : a < b) (hγ : 0 < γ) (_hγ' : γ < 1) (hT : 0 < T) :
    ∃ g : Net (Nat.succ d) 1,
      ∃ D : BlockDecomposition (gammaRadius γ (syntacticDepth g)) (Nat.succ d) 1,
        BlockDecomposition.toNet D = g ∧
        sSup (coordImage 0 (reach g X)) + T ≤ ubPr D X 0 := by
  let gap : Nat := Nat.ceil (3 / γ)
  let g : Net (Nat.succ d) 1 :=
    pumpNet (prefixNet (d := d) a b) (negValleyNet T) gap
  have hr : 3 ≤ gammaRadius γ (syntacticDepth g) := by
    simpa [g, gap] using
      (three_le_gammaRadius_pumpNet (prefixNet (d := d) a b) (negValleyNet T) hγ)
  have hprefix : layerCount (prefixNet (d := d) a b) ≤ gammaRadius γ (syntacticDepth g) := by
    simpa [prefixNet, normalizeNet, liftNet, g, gap] using hr
  have hnegValley : layerCount (negValleyNet T) ≤ gammaRadius γ (syntacticDepth g) := by
    simpa [negValleyNet, diffNet, sumNet, g, gap] using hr
  let D : BlockDecomposition (gammaRadius γ (syntacticDepth g)) (Nat.succ d) 1 :=
    pumpDecomposition (prefixNet (d := d) a b) hprefix (negValleyNet T) hnegValley gap
  refine ⟨g, D, ?_, ?_⟩
  · simp [D, g, gap, pumpDecomposition, pumpNet]
  let exactSet := coordImage 0 (reach g X)
  let relaxSet := coordImage 0 (PrRelax D X)
  have hXne : X.Nonempty := by
    rcases Theorem33.exists_mem_of_firstCoord hproj (by exact ⟨le_rfl, le_of_lt hab⟩) with
      ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  have hexact_nonempty : exactSet.Nonempty := by
    apply coordImage_nonempty 0
    exact reach_nonempty g hXne
  have hExact_le : ∀ r ∈ exactSet, r ≤ -T := by
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    have hy' : y ∈ reach (upperCounterexample (d := d) a b T) X := by
      simpa [exactSet, D, g, gap, upperCounterexample] using hy
    rcases hy' with ⟨x, hxX, rfl⟩
    have hx0 : x 0 ∈ Set.Icc a b := Theorem33.firstCoord_mem_Icc hproj hxX
    have hnorm : normalized a b (x 0) ∈ Set.Icc (-1 : Real) 1 :=
      normalized_mem_Icc hab hx0
    have hge : T ≤ valleyValue T (prefixPoint (normalized a b (x 0))) :=
      valleyValue_prefix_ge T (normalized a b (x 0)) hT hnorm
    have hneg : -valleyValue T (prefixPoint (normalized a b (x 0))) ≤ -T := by
      linarith
    simpa [upperCounterexample, eval_negValleyNet, eval_prefixNet] using hneg
  have hmax_le : sSup exactSet ≤ -T := csSup_le hexact_nonempty hExact_le
  have hmid : midPoint ∈ convexHull Real (reach (prefixNet (d := d) a b) X) :=
    midPoint_mem_convexHull_reach_prefix hproj hab
  have hzero_mem : (0 : Real) ∈ relaxSet := by
    have hreach_mid : (((fun _ : Fin 1 => (0 : Real)) : Coord 1)) ∈
        reach (negValleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X)) := by
      refine ⟨midPoint, hmid, ?_⟩
      ext i
      fin_cases i
      simp [eval_negValleyNet, valleyValue_at_midPoint]
    have hrel_mid : (((fun _ : Fin 1 => (0 : Real)) : Coord 1)) ∈ PrRelax D X := by
      rw [PrRelax_pumpDecomposition_eq]
      exact subset_convexHull Real _ hreach_mid
    exact ⟨((fun _ : Fin 1 => (0 : Real)) : Coord 1), hrel_mid, rfl⟩
  let K : Set (Coord 1) := {y | y 0 ≤ 0}
  have hK_conv : Convex Real K := by
    intro y hy z hz α β hα hβ hαβ
    dsimp [K] at hy hz ⊢
    nlinarith
  have hreach_nonpos :
      reach (negValleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X)) ⊆ K := by
    intro y hy
    rcases hy with ⟨z, -, rfl⟩
    dsimp [K]
    have hnonneg : 0 ≤ valleyValue T z := valleyValue_nonneg T (le_of_lt hT) z
    simpa [eval_negValleyNet] using (neg_nonpos.mpr hnonneg)
  have hrel_bddAbove : BddAbove relaxSet := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    have hyK : y ∈ K := by
      rw [PrRelax_pumpDecomposition_eq] at hy
      exact convexHull_min hreach_nonpos hK_conv hy
    simpa [K] using hyK
  have hzero_le_ub : 0 ≤ ubPr D X 0 := by
    simpa [ubPr, relaxSet] using le_csSup hrel_bddAbove hzero_mem
  linarith

/--
Semantic version of Theorem 4.2 for the explicit-decomposition cross-layer
relaxation.
-/
theorem theorem42
    {d : Nat} {X : Set (Coord (Nat.succ d))} {a b γ T : Real}
    (hXconv : Convex Real X)
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X = Set.Icc a b)
    (hab : a < b) (hγ : 0 < γ) (hγ' : γ < 1) (hT : 0 < T) :
    (∃ f : Net (Nat.succ d) 1,
        ∃ D : BlockDecomposition (gammaRadius γ (syntacticDepth f)) (Nat.succ d) 1,
          BlockDecomposition.toNet D = f ∧
          lbPr D X 0 ≤ sInf (coordImage 0 (reach f X)) - T) ∧
      (∃ g : Net (Nat.succ d) 1,
        ∃ D : BlockDecomposition (gammaRadius γ (syntacticDepth g)) (Nat.succ d) 1,
          BlockDecomposition.toNet D = g ∧
          sSup (coordImage 0 (reach g X)) + T ≤ ubPr D X 0) := by
  refine ⟨theorem42_lower hXconv hproj hab hγ hγ' hT,
    theorem42_upper hXconv hproj hab hγ hγ' hT⟩

end

end Theorem42

end Net

end MultiNeuron
