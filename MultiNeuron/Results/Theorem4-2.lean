import MultiNeuron.Results.«Lemma4-1»
import MultiNeuron.Results.auxNets

open Set

namespace Net

namespace Theorem42Polytope

noncomputable section

/-!
This file formalizes the fixed-radius sliding-window version of Theorem 4.2.
-/

namespace Theorem33Polytope

/--
Corresponds to `f'((ρ W₁ W₀) (X)) ≥ T` in the paper.
-/
theorem valleyValue_prefix_ge (T t : Real) (hT : 0 < T) (ht : t ∈ Set.Icc (-1 : Real) 1) :
    T ≤ valleyValue T (prefixPoint t) := by
  have hshift : 0 ≤ t + 1 := by linarith [ht.1]
  rcases le_or_gt t 0 with ht_nonpos | ht_pos
  · have hmax1 : max t 0 = 0 := max_eq_right ht_nonpos
    have hmaxShift : max (t + 1) 0 = t + 1 := max_eq_left hshift
    have hA : max (max (t + 1) 0 - 1) 0 = 0 := by
      rw [hmaxShift]
      simpa using hmax1
    have hB : max (1 - max (t + 1) 0) 0 = -t := by
      rw [hmaxShift]
      have : 0 ≤ -t := by linarith
      simpa [sub_eq_add_neg] using (max_eq_left this : max (-t) 0 = -t)
    have hC : max (max t 0 - (1 / 2 : Real)) 0 = 0 := by
      rw [hmax1]
      norm_num
    have hD : max ((1 / 2 : Real) - max t 0) 0 = (1 / 2 : Real) := by
      rw [hmax1]
      norm_num
    simp [valleyValue, prefixPoint]
    have hC' : max (max t 0 - (2⁻¹ : Real)) 0 = 0 := by simpa using hC
    have hD' : max ((2⁻¹ : Real) - max t 0) 0 = (1 / 2 : Real) := by simpa using hD
    rw [hA, hB, hC', hD']
    nlinarith [hT, ht.1]
  · rcases le_or_gt t (1 / 2 : Real) with ht_le_half | ht_gt_half
    · have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
      have hmax1 : max t 0 = t := max_eq_left ht_nonneg
      have hmaxShift : max (t + 1) 0 = t + 1 := max_eq_left hshift
      have hA : max (max (t + 1) 0 - 1) 0 = t := by
        rw [hmaxShift]
        simpa using hmax1
      have hB : max (1 - max (t + 1) 0) 0 = 0 := by
        rw [hmaxShift]
        have : 1 - (t + 1) ≤ 0 := by linarith
        simpa using (max_eq_right this : max (1 - (t + 1)) 0 = 0)
      have hC : max (max t 0 - (1 / 2 : Real)) 0 = 0 := by
        rw [hmax1]
        have : t - (1 / 2 : Real) ≤ 0 := by linarith
        simpa using (max_eq_right this : max (t - (1 / 2 : Real)) 0 = 0)
      have hD : max ((1 / 2 : Real) - max t 0) 0 = (1 / 2 : Real) - t := by
        rw [hmax1]
        have : 0 ≤ (1 / 2 : Real) - t := by linarith
        simpa using (max_eq_left this : max ((1 / 2 : Real) - t) 0 = (1 / 2 : Real) - t)
      simp [valleyValue, prefixPoint]
      have hC' : max (max t 0 - (2⁻¹ : Real)) 0 = 0 := by simpa using hC
      have hD' : max ((2⁻¹ : Real) - max t 0) 0 = (1 / 2 : Real) - t := by simpa using hD
      rw [hA, hB, hC', hD']
      ring_nf
      linarith
    · have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
      have hmax1 : max t 0 = t := max_eq_left ht_nonneg
      have hmaxShift : max (t + 1) 0 = t + 1 := max_eq_left hshift
      have hA : max (max (t + 1) 0 - 1) 0 = t := by
        rw [hmaxShift]
        simpa using hmax1
      have hB : max (1 - max (t + 1) 0) 0 = 0 := by
        rw [hmaxShift]
        have : 1 - (t + 1) ≤ 0 := by linarith
        simpa using (max_eq_right this : max (1 - (t + 1)) 0 = 0)
      have hC : max (max t 0 - (1 / 2 : Real)) 0 = t - (1 / 2 : Real) := by
        rw [hmax1]
        have : 0 ≤ t - (1 / 2 : Real) := by linarith
        simpa using (max_eq_left this : max (t - (1 / 2 : Real)) 0 = t - (1 / 2 : Real))
      have hD : max ((1 / 2 : Real) - max t 0) 0 = 0 := by
        rw [hmax1]
        have : (1 / 2 : Real) - t ≤ 0 := by linarith
        simpa using (max_eq_right this : max ((1 / 2 : Real) - t) 0 = 0)
      simp [valleyValue, prefixPoint]
      have hC' : max (max t 0 - (2⁻¹ : Real)) 0 = t - (1 / 2 : Real) := by simpa using hC
      have hD' : max ((2⁻¹ : Real) - max t 0) 0 = 0 := by simpa using hD
      rw [hA, hB, hC', hD']
      ring_nf
      nlinarith [hT, ht_gt_half]

/-- If the first-coordinate projection of `X` is `[a,b]`, then every `u ∈ [a,b]` is attained. -/
theorem exists_mem_of_firstCoord {d : Nat} {X : Polytope (Nat.succ d)} {a b u : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hu : u ∈ Set.Icc a b) :
    ∃ x ∈ X.feasibleSet, x 0 = u := by
  have hu' : u ∈ (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet := by
    simpa [hproj] using hu
  rcases hu' with ⟨x, hx, hxu⟩
  exact ⟨x, hx, hxu⟩

/-- If the first-coordinate projection of `X` is `[a,b]`, then every `x ∈ X` has first coordinate in `[a,b]`. -/
theorem firstCoord_mem_Icc {d : Nat} {X : Polytope (Nat.succ d)} {a b : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    {x : Coord (Nat.succ d)} (hx : x ∈ X.feasibleSet) :
    x 0 ∈ Set.Icc a b := by
  have hx' : x 0 ∈ (fun y : Coord (Nat.succ d) => y 0) '' X.feasibleSet := ⟨x, hx, rfl⟩
  rw [hproj] at hx'
  exact hx'

/-- The left endpoint of the broken line lies in the prefix reach set. -/
theorem leftPoint_in_reach_prefix {d : Nat} {X : Polytope (Nat.succ d)} {a b : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b) (hab : a < b) :
    leftPoint ∈ reach (prefixNet (d := d) a b) X.feasibleSet := by
  rcases exists_mem_of_firstCoord hproj (by exact ⟨le_rfl, le_of_lt hab⟩) with ⟨x, hxX, hx0⟩
  refine ⟨x, hxX, ?_⟩
  ext i
  fin_cases i
  · simp [eval_prefixNet, hx0, normalized_left hab, prefixPoint, leftPoint]
  · simp [eval_prefixNet, hx0, normalized_left hab, prefixPoint, leftPoint]

/-- The right endpoint of the broken line lies in the prefix reach set. -/
theorem rightPoint_in_reach_prefix {d : Nat} {X : Polytope (Nat.succ d)} {a b : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b) (hab : a < b) :
    rightPoint ∈ reach (prefixNet (d := d) a b) X.feasibleSet := by
  rcases exists_mem_of_firstCoord hproj (by exact ⟨le_of_lt hab, le_rfl⟩) with ⟨x, hxX, hx0⟩
  refine ⟨x, hxX, ?_⟩
  ext i
  fin_cases i
  · norm_num [eval_prefixNet, hx0, normalized_right hab, prefixPoint, rightPoint]
  · norm_num [eval_prefixNet, hx0, normalized_right hab, prefixPoint, rightPoint]

/-- The midpoint of the broken line lies in the convex hull of the prefix reach set. -/
theorem midPoint_mem_convexHull_reach_prefix {d : Nat} {X : Polytope (Nat.succ d)} {a b : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b) (hab : a < b) :
    midPoint ∈ convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet) := by
  have hleft : leftPoint ∈ convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet) :=
    subset_convexHull Real _ (leftPoint_in_reach_prefix hproj hab)
  have hright : rightPoint ∈ convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet) :=
    subset_convexHull Real _ (rightPoint_in_reach_prefix hproj hab)
  have hconv : Convex Real (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)) :=
    convex_convexHull Real _
  have hmid' : (1 / 2 : Real) • leftPoint + (1 / 2 : Real) • rightPoint ∈
      convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet) := by
    apply hconv hleft hright <;> norm_num
  simpa [leftPoint, rightPoint, midPoint] using hmid'

/-- For all `T ≥ 0`, the function computed by `valleyNet` is nonnegative. -/
theorem exact_valley_nonneg (T : Real) (hT : 0 ≤ T) (y : Coord 2) :
    0 ≤ eval (valleyNet T) y 0 := by
  simpa [eval_valleyNet] using valleyValue_nonneg T hT y

/-- For all `T ≥ 0`, the function computed by `negValleyNet` is nonpositive. -/
theorem exact_negValley_nonpos (T : Real) (hT : 0 ≤ T) (y : Coord 2) :
    eval (negValleyNet T) y 0 ≤ 0 := by
  have hnonneg : 0 ≤ valleyValue T y := valleyValue_nonneg T hT y
  simpa [eval_negValleyNet] using (neg_nonpos.mpr hnonneg : -valleyValue T y ≤ 0)

end Theorem33Polytope

/--
Fixed-radius sliding-window lower-bound half of Theorem 4.2.
-/
theorem theorem42_lower_fixedr
    {d : Nat} (X : Polytope (Nat.succ d)) {a b T : Real} {r : Nat}
    (hr : 0 < r) (hr3 : 3 ≤ r)
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hab : a < b) (hT : 0 < T)
    (hglue :
      PumpGlueCondition hr (prefixNet (d := d) a b) (valleyNet T) X.feasibleSet)
    (hPr_bdd :
      Bornology.IsBounded
        (PrOutputSetOnPolytope hr
          (pumpNetPr (prefixNet (d := d) a b) (valleyNet T) r) X)) :
    ∃ f : Net (Nat.succ d) 1,
      lbPrActual hr f X 0 ≤ lbproj 0 (reach f X.feasibleSet) - T := by
  let f : Net (Nat.succ d) 1 :=
    pumpNetPr (prefixNet (d := d) a b) (valleyNet T) r
  have hprefix : layerCount (prefixNet (d := d) a b) ≤ r := by
    simpa [prefixNet, normalize1DNet, liftNet] using hr3
  have hvalley : layerCount (valleyNet T) ≤ r := by
    simpa [valleyNet, absNet, sumNet] using hr3
  refine ⟨f, ?_⟩
  let exactSet := proj 0 (reach f X.feasibleSet)
  have hXne : X.feasibleSet.Nonempty := by
    rcases Theorem33Polytope.exists_mem_of_firstCoord hproj
      (by exact ⟨le_rfl, le_of_lt hab⟩) with ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  have hexact_nonempty : exactSet.Nonempty := by
    apply proj_nonempty 0
    exact reach_nonempty f hXne
  have hExact_ge : ∀ s ∈ exactSet, T ≤ s := by
    intro s hs
    rcases hs with ⟨y, hy, rfl⟩
    have hy' : y ∈ reach (lowerCounterexample (d := d) a b T) X.feasibleSet := by
      simpa [exactSet, f, lowerCounterexample] using hy
    rcases hy' with ⟨x, hxX, rfl⟩
    have hx0 : x 0 ∈ Set.Icc a b := Theorem33Polytope.firstCoord_mem_Icc hproj hxX
    have hnorm : normalized a b (x 0) ∈ Set.Icc (-1 : Real) 1 :=
      normalized_mem_Icc hab hx0
    simpa [lowerCounterexample, eval_valleyNet, eval_prefixNet] using
      Theorem33Polytope.valleyValue_prefix_ge T (normalized a b (x 0)) hT hnorm
  have hmin_ge : T ≤ lbproj 0 (reach f X.feasibleSet) := by
    simpa [lbproj, exactSet] using le_csInf hexact_nonempty hExact_ge
  have hlemma :
      lbPrActual hr f X 0 ≤
        lbproj 0 (reach (valleyNet T)
          (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by
    simpa [f] using
      lemma41_fixedr_lower (prefixNet (d := d) a b) (valleyNet T) X hr
        hprefix hvalley hXne hglue hPr_bdd
  have hreach_mid : (![(0 : Real)] : Coord 1) ∈
      reach (valleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)) := by
    refine ⟨midPoint, Theorem33Polytope.midPoint_mem_convexHull_reach_prefix hproj hab, ?_⟩
    ext i
    fin_cases i
    simp [eval_valleyNet, valleyValue_at_midPoint]
  have hzero_mem : (0 : Real) ∈
      proj 0 (reach (valleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by
    exact ⟨![0], hreach_mid, rfl⟩
  have hconv_bddBelow : BddBelow
      (proj 0 (reach (valleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)))) := by
    refine ⟨0, ?_⟩
    intro s hs
    rcases hs with ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    exact Theorem33Polytope.exact_valley_nonneg T (le_of_lt hT) z
  have hlb_le_zero :
      lbproj 0 (reach (valleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) ≤ 0 := by
    simpa [lbproj, proj] using csInf_le hconv_bddBelow hzero_mem
  have hlbPr_le_zero : lbPrActual hr f X 0 ≤ 0 := le_trans hlemma hlb_le_zero
  linarith

/--
Fixed-radius sliding-window upper-bound half of Theorem 4.2.
-/
theorem theorem42_upper_fixedr
    {d : Nat} (X : Polytope (Nat.succ d)) {a b T : Real} {r : Nat}
    (hr : 0 < r) (hr3 : 3 ≤ r)
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hab : a < b) (hT : 0 < T)
    (hglue :
      PumpGlueCondition hr (prefixNet (d := d) a b) (negValleyNet T) X.feasibleSet)
    (hPr_bdd :
      Bornology.IsBounded
        (PrOutputSetOnPolytope hr
          (pumpNetPr (prefixNet (d := d) a b) (negValleyNet T) r) X)) :
    ∃ g : Net (Nat.succ d) 1,
      ubproj 0 (reach g X.feasibleSet) + T ≤ ubPrActual hr g X 0 := by
  let g : Net (Nat.succ d) 1 :=
    pumpNetPr (prefixNet (d := d) a b) (negValleyNet T) r
  have hprefix : layerCount (prefixNet (d := d) a b) ≤ r := by
    simpa [prefixNet, normalize1DNet, liftNet] using hr3
  have hnegValley : layerCount (negValleyNet T) ≤ r := by
    simpa [negValleyNet, absNet, sumNet] using hr3
  refine ⟨g, ?_⟩
  let exactSet := proj 0 (reach g X.feasibleSet)
  have hXne : X.feasibleSet.Nonempty := by
    rcases Theorem33Polytope.exists_mem_of_firstCoord hproj
      (by exact ⟨le_rfl, le_of_lt hab⟩) with ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  have hexact_nonempty : exactSet.Nonempty := by
    apply proj_nonempty 0
    exact reach_nonempty g hXne
  have hExact_le : ∀ s ∈ exactSet, s ≤ -T := by
    intro s hs
    rcases hs with ⟨y, hy, rfl⟩
    have hy' : y ∈ reach (upperCounterexample (d := d) a b T) X.feasibleSet := by
      simpa [exactSet, g, upperCounterexample] using hy
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
      ubproj 0 (reach (negValleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) ≤
      ubPrActual hr g X 0 := by
    simpa [g] using
      lemma41_fixedr_upper (prefixNet (d := d) a b) (negValleyNet T) X hr
        hprefix hnegValley hXne hglue hPr_bdd
  have hreach_mid : (![(0 : Real)] : Coord 1) ∈
      reach (negValleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)) := by
    refine ⟨midPoint, Theorem33Polytope.midPoint_mem_convexHull_reach_prefix hproj hab, ?_⟩
    ext i
    fin_cases i
    simp [eval_negValleyNet, valleyValue_at_midPoint]
  have hzero_mem : (0 : Real) ∈
      proj 0 (reach (negValleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by
    exact ⟨![0], hreach_mid, rfl⟩
  have hconv_bddAbove : BddAbove
      (proj 0 (reach (negValleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)))) := by
    refine ⟨0, ?_⟩
    intro s hs
    rcases hs with ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    exact Theorem33Polytope.exact_negValley_nonpos T (le_of_lt hT) z
  have hzero_le_ub :
      0 ≤ ubproj 0 (reach (negValleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by
    simpa [ubproj, proj] using le_csSup hconv_bddAbove hzero_mem
  have hzero_le_ubPr : 0 ≤ ubPrActual hr g X 0 := le_trans hzero_le_ub hlemma
  linarith

/-- Fixed-radius version of Theorem 4.2. -/
theorem theorem42_fixedr
    {d : Nat} (X : Polytope (Nat.succ d)) {a b T : Real} {r : Nat}
    (hr : 0 < r) (hr3 : 3 ≤ r)
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hab : a < b) (hT : 0 < T)
    (hglueLower :
      PumpGlueCondition hr (prefixNet (d := d) a b) (valleyNet T) X.feasibleSet)
    (hPrLower_bdd :
      Bornology.IsBounded
        (PrOutputSetOnPolytope hr
          (pumpNetPr (prefixNet (d := d) a b) (valleyNet T) r) X))
    (hglueUpper :
      PumpGlueCondition hr (prefixNet (d := d) a b) (negValleyNet T) X.feasibleSet)
    (hPrUpper_bdd :
      Bornology.IsBounded
        (PrOutputSetOnPolytope hr
          (pumpNetPr (prefixNet (d := d) a b) (negValleyNet T) r) X)) :
    (∃ f : Net (Nat.succ d) 1,
        lbPrActual hr f X 0 ≤ lbproj 0 (reach f X.feasibleSet) - T) ∧
      (∃ g : Net (Nat.succ d) 1,
        ubproj 0 (reach g X.feasibleSet) + T ≤ ubPrActual hr g X 0) := by
  refine ⟨theorem42_lower_fixedr X hr hr3 hproj hab hT hglueLower hPrLower_bdd,
    theorem42_upper_fixedr X hr hr3 hproj hab hT hglueUpper hPrUpper_bdd⟩

/--
changing-r-version lower-bound half of Theorem 4.2.
`r = max (1, floor (α * L))`.
-/
theorem theorem42_lower
    {d : Nat} (X : Polytope (Nat.succ d)) {a b T α : Real}
    (hα : α < 1)
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hab : a < b) (hT : 0 < T)
    (s : Nat)
    (hlarge :
      let r := alphaRadius α
        (layerCount (pumpNetPr (prefixNet (d := d) a b) (valleyNet T) s))
      r ≤ s)
    (hglue :
      let r := alphaRadius α
        (layerCount (pumpNetPr (prefixNet (d := d) a b) (valleyNet T) s))
      let hr : 0 < r := alphaRadius_pos α
        (layerCount (pumpNetPr (prefixNet (d := d) a b) (valleyNet T) s))
      let f₂' := prependIds (2 * (s - r)) (valleyNet T)
      let left : LayerChain.T (Nat.succ d) 2 :=
        LayerChain.appendChain
          (LayerChain.FlattenNet (prefixNet (d := d) a b))
          (LayerChain.idChain 2 r)
      let right : LayerChain.T 2 1 :=
        LayerChain.appendChain (LayerChain.idChain 2 r) (LayerChain.FlattenNet f₂')
      let whole : LayerChain.T (Nat.succ d) 1 := LayerChain.appendChain left right
      ∀ {u : FullTrace left} {v : FullTrace right},
        u ∈ convHullTrace left X.feasibleSet →
        v ∈ PrRelaxedSetChain r hr right {traceOutput u} →
        LayerChain.spliceTrace u v ∈ PrRelaxedSetChain r hr whole X.feasibleSet)
    (hPr_bdd :
      Bornology.IsBounded
        (PrOutputSetOnPolytope
          (alphaRadius_pos α
            (layerCount (pumpNetPr (prefixNet (d := d) a b) (valleyNet T) s)))
          (pumpNetPr (prefixNet (d := d) a b) (valleyNet T) s) X)) :
    ∃ f : Net (Nat.succ d) 1,
      lbPrActual (alphaRadius_pos α (layerCount f)) f X 0 ≤
        lbproj 0 (reach f X.feasibleSet) - T := by
  let f : Net (Nat.succ d) 1 :=
    pumpNetPr (prefixNet (d := d) a b) (valleyNet T) s
  refine ⟨f, ?_⟩
  let hr : 0 < alphaRadius α (layerCount f) := alphaRadius_pos α (layerCount f)
  let exactSet := proj 0 (reach f X.feasibleSet)
  have hXne : X.feasibleSet.Nonempty := by
    rcases Theorem33Polytope.exists_mem_of_firstCoord hproj
      (by exact ⟨le_rfl, le_of_lt hab⟩) with ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  have hexact_nonempty : exactSet.Nonempty := by
    apply proj_nonempty 0
    exact reach_nonempty f hXne
  have hExact_ge : ∀ u ∈ exactSet, T ≤ u := by
    intro u hu
    rcases hu with ⟨y, hy, rfl⟩
    have hy' : y ∈ reach (lowerCounterexample (d := d) a b T) X.feasibleSet := by
      simpa [exactSet, f, lowerCounterexample] using hy
    rcases hy' with ⟨x, hxX, rfl⟩
    have hx0 : x 0 ∈ Set.Icc a b := Theorem33Polytope.firstCoord_mem_Icc hproj hxX
    have hnorm : normalized a b (x 0) ∈ Set.Icc (-1 : Real) 1 :=
      normalized_mem_Icc hab hx0
    simpa [lowerCounterexample, eval_valleyNet, eval_prefixNet] using
      Theorem33Polytope.valleyValue_prefix_ge T (normalized a b (x 0)) hT hnorm
  have hmin_ge : T ≤ lbproj 0 (reach f X.feasibleSet) := by
    simpa [lbproj, exactSet] using le_csInf hexact_nonempty hExact_ge
  have hlemma :
      lbPrActual hr f X 0 ≤
        lbproj 0 (reach (valleyNet T)
          (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by
    have hPr_bdd' :
        Bornology.IsBounded
          (PrOutputSet
            (alphaRadius_pos α (layerCount f))
            f X.feasibleSet) := by
      simpa [f, PrOutputSetOnPolytope] using hPr_bdd
    have hrad :
        lbproj 0 (reach (valleyNet T)
          (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) ≥
          lbproj 0
            (PrOutputSet
              (alphaRadius_pos α (layerCount f))
              f X.feasibleSet) := by
      simpa [f] using
        lemma41_lower α hα (prefixNet (d := d) a b) (valleyNet T) s X.feasibleSet
          hXne hlarge hglue hPr_bdd'
    simpa [lbPrActual, PrOutputSetOnPolytope, hr, ge_iff_le] using hrad
  have hreach_mid : (![(0 : Real)] : Coord 1) ∈
      reach (valleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)) := by
    refine ⟨midPoint, Theorem33Polytope.midPoint_mem_convexHull_reach_prefix hproj hab, ?_⟩
    ext i
    fin_cases i
    simp [eval_valleyNet, valleyValue_at_midPoint]
  have hzero_mem : (0 : Real) ∈
      proj 0 (reach (valleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by
    exact ⟨![0], hreach_mid, rfl⟩
  have hconv_bddBelow : BddBelow
      (proj 0 (reach (valleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)))) := by
    refine ⟨0, ?_⟩
    intro u hu
    rcases hu with ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    exact Theorem33Polytope.exact_valley_nonneg T (le_of_lt hT) z
  have hlb_le_zero :
      lbproj 0 (reach (valleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) ≤ 0 := by
    simpa [lbproj, proj] using csInf_le hconv_bddBelow hzero_mem
  have hlbPr_le_zero : lbPrActual hr f X 0 ≤ 0 := le_trans hlemma hlb_le_zero
  simpa [f, hr] using (show lbPrActual hr f X 0 ≤ lbproj 0 (reach f X.feasibleSet) - T by
    linarith)

/--
changing-r-version upper-bound half of Theorem 4.2.
-/
theorem theorem42_upper
    {d : Nat} (X : Polytope (Nat.succ d)) {a b T α : Real}
    (hα : α < 1)
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hab : a < b) (hT : 0 < T)
    (s : Nat)
    (hlarge :
      let r := alphaRadius α
        (layerCount (pumpNetPr (prefixNet (d := d) a b) (negValleyNet T) s))
      r ≤ s)
    (hglue :
      let r := alphaRadius α
        (layerCount (pumpNetPr (prefixNet (d := d) a b) (negValleyNet T) s))
      let hr : 0 < r := alphaRadius_pos α
        (layerCount (pumpNetPr (prefixNet (d := d) a b) (negValleyNet T) s))
      let f₂' := prependIds (2 * (s - r)) (negValleyNet T)
      let left : LayerChain.T (Nat.succ d) 2 :=
        LayerChain.appendChain
          (LayerChain.FlattenNet (prefixNet (d := d) a b))
          (LayerChain.idChain 2 r)
      let right : LayerChain.T 2 1 :=
        LayerChain.appendChain (LayerChain.idChain 2 r) (LayerChain.FlattenNet f₂')
      let whole : LayerChain.T (Nat.succ d) 1 := LayerChain.appendChain left right
      ∀ {u : FullTrace left} {v : FullTrace right},
        u ∈ convHullTrace left X.feasibleSet →
        v ∈ PrRelaxedSetChain r hr right {traceOutput u} →
        LayerChain.spliceTrace u v ∈ PrRelaxedSetChain r hr whole X.feasibleSet)
    (hPr_bdd :
      Bornology.IsBounded
        (PrOutputSetOnPolytope
          (alphaRadius_pos α
            (layerCount (pumpNetPr (prefixNet (d := d) a b) (negValleyNet T) s)))
          (pumpNetPr (prefixNet (d := d) a b) (negValleyNet T) s) X)) :
    ∃ g : Net (Nat.succ d) 1,
      ubproj 0 (reach g X.feasibleSet) + T ≤
        ubPrActual (alphaRadius_pos α (layerCount g)) g X 0 := by
  let g : Net (Nat.succ d) 1 :=
    pumpNetPr (prefixNet (d := d) a b) (negValleyNet T) s
  refine ⟨g, ?_⟩
  let hr : 0 < alphaRadius α (layerCount g) := alphaRadius_pos α (layerCount g)
  let exactSet := proj 0 (reach g X.feasibleSet)
  have hXne : X.feasibleSet.Nonempty := by
    rcases Theorem33Polytope.exists_mem_of_firstCoord hproj
      (by exact ⟨le_rfl, le_of_lt hab⟩) with ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  have hexact_nonempty : exactSet.Nonempty := by
    apply proj_nonempty 0
    exact reach_nonempty g hXne
  have hExact_le : ∀ u ∈ exactSet, u ≤ -T := by
    intro u hu
    rcases hu with ⟨y, hy, rfl⟩
    have hy' : y ∈ reach (upperCounterexample (d := d) a b T) X.feasibleSet := by
      simpa [exactSet, g, upperCounterexample] using hy
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
      ubproj 0 (reach (negValleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) ≤
        ubPrActual hr g X 0 := by
    have hPr_bdd' :
        Bornology.IsBounded
          (PrOutputSet
            (alphaRadius_pos α (layerCount g))
            g X.feasibleSet) := by
      simpa [g, PrOutputSetOnPolytope] using hPr_bdd
    have hrad :
        ubproj 0 (reach (negValleyNet T)
          (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) ≤
          ubproj 0
            (PrOutputSet
              (alphaRadius_pos α (layerCount g))
              g X.feasibleSet) := by
      simpa [g] using
        lemma41_upper α hα (prefixNet (d := d) a b) (negValleyNet T) s X.feasibleSet
          hXne hlarge hglue hPr_bdd'
    simpa [ubPrActual, PrOutputSetOnPolytope, hr] using hrad
  have hreach_mid : (![(0 : Real)] : Coord 1) ∈
      reach (negValleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)) := by
    refine ⟨midPoint, Theorem33Polytope.midPoint_mem_convexHull_reach_prefix hproj hab, ?_⟩
    ext i
    fin_cases i
    simp [eval_negValleyNet, valleyValue_at_midPoint]
  have hzero_mem : (0 : Real) ∈
      proj 0 (reach (negValleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by
    exact ⟨![0], hreach_mid, rfl⟩
  have hconv_bddAbove : BddAbove
      (proj 0 (reach (negValleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)))) := by
    refine ⟨0, ?_⟩
    intro u hu
    rcases hu with ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    exact Theorem33Polytope.exact_negValley_nonpos T (le_of_lt hT) z
  have hzero_le_ub :
      0 ≤ ubproj 0 (reach (negValleyNet T)
        (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by
    simpa [ubproj, proj] using le_csSup hconv_bddAbove hzero_mem
  have hzero_le_ubPr : 0 ≤ ubPrActual hr g X 0 := le_trans hzero_le_ub hlemma
  simpa [g, hr] using (show ubproj 0 (reach g X.feasibleSet) + T ≤ ubPrActual hr g X 0 by
    linarith)

/-- Changing-radius version of Theorem 4.2. -/
theorem theorem42
    {d : Nat} (X : Polytope (Nat.succ d)) {a b T α : Real}
    (hα : α < 1)
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hab : a < b) (hT : 0 < T)
    (s : Nat)
    (hlargeLower :
      let r := alphaRadius α
        (layerCount (pumpNetPr (prefixNet (d := d) a b) (valleyNet T) s))
      r ≤ s)
    (hglueLower :
      let r := alphaRadius α
        (layerCount (pumpNetPr (prefixNet (d := d) a b) (valleyNet T) s))
      let hr : 0 < r := alphaRadius_pos α
        (layerCount (pumpNetPr (prefixNet (d := d) a b) (valleyNet T) s))
      let f₂' := prependIds (2 * (s - r)) (valleyNet T)
      let left : LayerChain.T (Nat.succ d) 2 :=
        LayerChain.appendChain
          (LayerChain.FlattenNet (prefixNet (d := d) a b))
          (LayerChain.idChain 2 r)
      let right : LayerChain.T 2 1 :=
        LayerChain.appendChain (LayerChain.idChain 2 r) (LayerChain.FlattenNet f₂')
      let whole : LayerChain.T (Nat.succ d) 1 := LayerChain.appendChain left right
      ∀ {u : FullTrace left} {v : FullTrace right},
        u ∈ convHullTrace left X.feasibleSet →
        v ∈ PrRelaxedSetChain r hr right {traceOutput u} →
        LayerChain.spliceTrace u v ∈ PrRelaxedSetChain r hr whole X.feasibleSet)
    (hPrLower_bdd :
      Bornology.IsBounded
        (PrOutputSetOnPolytope
          (alphaRadius_pos α
            (layerCount (pumpNetPr (prefixNet (d := d) a b) (valleyNet T) s)))
          (pumpNetPr (prefixNet (d := d) a b) (valleyNet T) s) X))
    (hlargeUpper :
      let r := alphaRadius α
        (layerCount (pumpNetPr (prefixNet (d := d) a b) (negValleyNet T) s))
      r ≤ s)
    (hglueUpper :
      let r := alphaRadius α
        (layerCount (pumpNetPr (prefixNet (d := d) a b) (negValleyNet T) s))
      let hr : 0 < r := alphaRadius_pos α
        (layerCount (pumpNetPr (prefixNet (d := d) a b) (negValleyNet T) s))
      let f₂' := prependIds (2 * (s - r)) (negValleyNet T)
      let left : LayerChain.T (Nat.succ d) 2 :=
        LayerChain.appendChain
          (LayerChain.FlattenNet (prefixNet (d := d) a b))
          (LayerChain.idChain 2 r)
      let right : LayerChain.T 2 1 :=
        LayerChain.appendChain (LayerChain.idChain 2 r) (LayerChain.FlattenNet f₂')
      let whole : LayerChain.T (Nat.succ d) 1 := LayerChain.appendChain left right
      ∀ {u : FullTrace left} {v : FullTrace right},
        u ∈ convHullTrace left X.feasibleSet →
        v ∈ PrRelaxedSetChain r hr right {traceOutput u} →
        LayerChain.spliceTrace u v ∈ PrRelaxedSetChain r hr whole X.feasibleSet)
    (hPrUpper_bdd :
      Bornology.IsBounded
        (PrOutputSetOnPolytope
          (alphaRadius_pos α
            (layerCount (pumpNetPr (prefixNet (d := d) a b) (negValleyNet T) s)))
          (pumpNetPr (prefixNet (d := d) a b) (negValleyNet T) s) X)) :
    (∃ f : Net (Nat.succ d) 1,
        lbPrActual (alphaRadius_pos α (layerCount f)) f X 0 ≤
          lbproj 0 (reach f X.feasibleSet) - T) ∧
      (∃ g : Net (Nat.succ d) 1,
        ubproj 0 (reach g X.feasibleSet) + T ≤
          ubPrActual (alphaRadius_pos α (layerCount g)) g X 0) := by
  refine ⟨theorem42_lower X hα hproj hab hT s hlargeLower hglueLower hPrLower_bdd,
    theorem42_upper X hα hproj hab hT s hlargeUpper hglueUpper hPrUpper_bdd⟩


end

end Theorem42Polytope

end Net
