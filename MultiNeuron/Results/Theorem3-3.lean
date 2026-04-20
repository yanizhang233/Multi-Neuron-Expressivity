
import MultiNeuron.Results.«Lemma3-2»
import MultiNeuron.Results.auxNets
open Set

namespace Net

namespace Theorem33Polytope

noncomputable section

/-!
This file formalizes Theorem 3.3 in the paper.
-/

/-- The broken line traced by `prefixPoint` over the interval `[-1,1]`. -/
def prefixBrokenLine : Set (Coord 2) :=
  {y | (0 ≤ y 0 ∧ y 0 ≤ 1 ∧ y 1 = 0) ∨
      (1 ≤ y 0 ∧ y 0 ≤ 2 ∧ y 1 = y 0 - 1)}

/-- The affine normalization sends `[a,b]` exactly to `[-1,1]`. -/
theorem normalized_image_Icc {a b : Real} (hab : a < b) :
    normalized a b '' Set.Icc a b = Set.Icc (-1 : Real) 1 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact normalized_mem_Icc hab hu
  · intro ht
    let u : Real := ((b - a) * t + (a + b)) / 2
    have hba : 0 < b - a := sub_pos.mpr hab
    have hu : u ∈ Set.Icc a b := by
      constructor
      · dsimp [u]
        have hleft : -(b - a) ≤ (b - a) * t := by
          nlinarith [ht.1, hba]
        linarith
      · dsimp [u]
        have hright : (b - a) * t ≤ b - a := by
          nlinarith [ht.2, hba]
        linarith
    refine ⟨u, hu, ?_⟩
    have hden : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
    dsimp [u, normalized]
    field_simp [hden]
    ring

/-- The image of `prefixPoint` on `[-1,1]` is exactly the target broken line. -/
theorem prefixPoint_image_Icc :
    prefixPoint '' Set.Icc (-1 : Real) 1 = prefixBrokenLine := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hshift : 0 ≤ t + 1 := by linarith [ht.1]
    rcases le_or_gt t 0 with ht_nonpos | ht_pos
    · left
      refine ⟨?_, ?_, ?_⟩
      · simpa [prefixPoint, max_eq_left hshift] using hshift
      · have hupper : t + 1 ≤ 1 := by linarith
        simpa [prefixPoint, max_eq_left hshift] using hupper
      · simp [prefixPoint, max_eq_right ht_nonpos]
    · have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
      right
      refine ⟨?_, ?_, ?_⟩
      · have hlower : 1 ≤ t + 1 := by linarith
        simpa [prefixPoint, max_eq_left hshift] using hlower
      · have hupper : t + 1 ≤ 2 := by linarith [ht.2]
        simpa [prefixPoint, max_eq_left hshift] using hupper
      · simp [prefixPoint, max_eq_left hshift, max_eq_left ht_nonneg]
  · rintro (⟨hy0_nonneg, hy0_le_one, hy1⟩ | ⟨hy0_ge_one, hy0_le_two, hy1⟩)
    · refine ⟨y 0 - 1, ?_, ?_⟩
      · constructor <;> linarith
      · have hy : y = ![y 0, y 1] := by
          ext i
          fin_cases i <;> rfl
        rw [hy]
        ext i
        fin_cases i
        · have hcoord : 0 ≤ y 0 := hy0_nonneg
          simp [prefixPoint, max_eq_left hcoord]
        · have hnonpos : y 0 - 1 ≤ 0 := by linarith
          simp [prefixPoint, max_eq_right hnonpos, hy1]
    · refine ⟨y 0 - 1, ?_, ?_⟩
      · constructor <;> linarith
      · have hy : y = ![y 0, y 1] := by
          ext i
          fin_cases i <;> rfl
        rw [hy]
        ext i
        fin_cases i
        · have hcoord : 0 ≤ y 0 := by linarith
          simp [prefixPoint, max_eq_left hcoord]
        · have hnonneg : 0 ≤ y 0 - 1 := by linarith
          simp [prefixPoint, max_eq_left hnonneg, hy1]

/--
If a polytope projects to `[a,b]` on the first coordinate, then the reachable
set of the prefix network is exactly the broken line
`{(x,y) : 0 ≤ x ≤ 1, y = 0} ∪ {(x,y) : 1 ≤ x ≤ 2, y = x - 1}`.
-/
theorem reach_prefix_eq_prefixBrokenLine {d : Nat} (X : Polytope (Nat.succ d)) {a b : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hab : a < b) :
    reach (prefixNet (d := d) a b) X.feasibleSet = prefixBrokenLine := by
  calc
    reach (prefixNet (d := d) a b) X.feasibleSet
        = (fun x : Coord (Nat.succ d) => prefixPoint (normalized a b (x 0))) '' X.feasibleSet := by
            ext y
            simp [Net.reach, eval_prefixNet]
    _ = prefixPoint '' (normalized a b '' ((fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet)) := by
          ext y
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact ⟨normalized a b (x 0), ⟨x 0, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
          · rintro ⟨t, ⟨u, ⟨x, hx, hxu⟩, hut⟩, hty⟩
            subst hxu
            subst hut
            exact ⟨x, hx, hty⟩
    _ = prefixPoint '' (normalized a b '' Set.Icc a b) := by rw [hproj]
    _ = prefixPoint '' Set.Icc (-1 : Real) 1 := by rw [normalized_image_Icc hab]
    _ = prefixBrokenLine := prefixPoint_image_Icc






/--
corresponds to f'((ρ W₁ W₀) (X)) ≥ T in the paper
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

/-- if projecting a convex polytope X onto the first coordinate gives [a,b], then for every point u ∈ [a,b], exists a point x in the convex polytope that projects to u. -/
theorem exists_mem_of_firstCoord {d : Nat} {X : Polytope (Nat.succ d)} {a b u : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hu : u ∈ Set.Icc a b) :
    ∃ x ∈ X.feasibleSet, x 0 = u := by
  have hu' : u ∈ (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet := by simpa [hproj] using hu
  rcases hu' with ⟨x, hx, hxu⟩
  exact ⟨x, hx, hxu⟩

/-- if projecting a convex polytope X onto the first coordinate gives [a,b], then for every point x ∈ X, the first coordinate of x falls into [a,b]  -/
theorem firstCoord_mem_Icc {d : Nat} {X : Polytope (Nat.succ d)} {a b : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    {x : Coord (Nat.succ d)} (hx : x ∈ X.feasibleSet) :
    x 0 ∈ Set.Icc a b := by
  have hx' : x 0 ∈ (fun y : Coord (Nat.succ d) => y 0) '' X.feasibleSet := ⟨x, hx, rfl⟩
  rw[hproj] at hx'
  assumption

/-- X is a convex polytope whose projection on the first coordinate is [a,b], the output set of prefixNet on input X covers the leftpoint (0,0)-/
theorem leftPoint_in_reach_prefix {d : Nat} {X : Polytope (Nat.succ d)} {a b : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b) (hab : a < b) :
    leftPoint ∈ reach (prefixNet (d := d) a b) X.feasibleSet := by
  rcases exists_mem_of_firstCoord hproj (by exact ⟨le_rfl, le_of_lt hab⟩) with ⟨x, hxX, hx0⟩
  refine ⟨x, hxX, ?_⟩
  ext i
  fin_cases i
  · simp [eval_prefixNet, hx0, normalized_left hab, prefixPoint, leftPoint]
  · simp [eval_prefixNet, hx0, normalized_left hab, prefixPoint, leftPoint]

/-- X is a convex polytope whose projection on the first coordinate is [a,b], the output set of prefixNet on input X covers the right point (2,1)-/
theorem rightPoint_in_reach_prefix {d : Nat} {X : Polytope (Nat.succ d)} {a b : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b) (hab : a < b) :
    rightPoint ∈ reach (prefixNet (d := d) a b) X.feasibleSet := by
  rcases exists_mem_of_firstCoord hproj (by exact ⟨le_of_lt hab, le_rfl⟩) with ⟨x, hxX, hx0⟩
  refine ⟨x, hxX, ?_⟩
  ext i
  fin_cases i
  · norm_num [eval_prefixNet, hx0, normalized_right hab, prefixPoint, rightPoint]
  · norm_num [eval_prefixNet, hx0, normalized_right hab, prefixPoint, rightPoint]


/-- X is a convex polytope whose projection on the first coordinate is [a,b], the convex hull of the output set of prefixNet on input X covers the mid point (1, 0.5)
-/
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

/--
for all T ≥ 0, the function computed by valleyNet is ≥ 0.
-/
theorem exact_valley_nonneg (T : Real) (hT : 0 ≤ T) (y : Coord 2) :
    0 ≤ eval (valleyNet T) y 0 := by
  simpa [eval_valleyNet] using valleyValue_nonneg T hT y


/--
for all T ≥ 0, the function computed by valleyNet is ≤ 0.
-/

theorem exact_negValley_nonpos (T : Real) (hT : 0 ≤ T) (y : Coord 2) :
    eval (negValleyNet T) y 0 ≤ 0 := by
  have hnonneg : 0 ≤ valleyValue T y := valleyValue_nonneg T hT y
  simpa [eval_negValleyNet] using (neg_nonpos.mpr hnonneg : -valleyValue T y ≤ 0)

/--X is a convex polytope whose projection on the first coordinate is [a,b], for the network 'lowerCounterexample',
its lower bound returned by P₁ on X is ≤ ground_truth lower bound - T
-/

theorem theorem33Polytope_lower
    {d : Nat} (X : Polytope (Nat.succ d)) {a b T : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hab : a < b) (hT : 0 < T) :
    lbP1 (lowerCounterexample (d := d) a b T) X 0 ≤
      lbproj 0 (reach (lowerCounterexample (d := d) a b T) X.feasibleSet) - T := by
  let f := lowerCounterexample (d := d) a b T --the network 'lowerCounterexample'
  let exactSet := proj 0 (reach f X.feasibleSet)
  have hXne : X.feasibleSet.Nonempty := by -- input set X is nonempty
    rcases exists_mem_of_firstCoord hproj (by exact ⟨le_rfl, le_of_lt hab⟩) with ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  have hexact_nonempty : exactSet.Nonempty := by -- exact reachable set is nonempty
    apply proj_nonempty 0
    exact reach_nonempty f hXne
  have hExact_ge : ∀ r ∈ exactSet, T ≤ r := by -- every function value is ≥ T.
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    rcases hy with ⟨x, hxX, rfl⟩
    have hx0 : x 0 ∈ Set.Icc a b := firstCoord_mem_Icc hproj hxX
    have hnorm : normalized a b (x 0) ∈ Set.Icc (-1 : Real) 1 := normalized_mem_Icc hab hx0
    simpa [f, lowerCounterexample, eval_valleyNet, eval_prefixNet] using
      valleyValue_prefix_ge T (normalized a b (x 0)) hT hnorm
  have hmin_ge : T ≤ lbproj 0 (reach f X.feasibleSet) := by -- the ground truth lower bound is ≥ T.
    simpa [lbproj, exactSet] using le_csInf hexact_nonempty hExact_ge
  have hlemma : lbP1 f X 0 ≤ lbproj 0 (reach (valleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by -- ℓ(f, X, P₁) ≤ min f₂ (conv (f(X)))
    simpa [f, lowerCounterexample] using lemma32Polytope_lower (prefixNet (d := d) a b) (valleyNet T) X 0 hXne
  have hreach_mid : ((![0] : Coord 1)) ∈ reach (valleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)) := by -- 0 ∈ f₂ (conv (f(X)))
  --(((fun _ : Fin 1 => (0 : Real)) : Coord 1)) ∈ reach (valleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)) := by
    refine ⟨midPoint, midPoint_mem_convexHull_reach_prefix hproj hab, ?_⟩
    ext i
    fin_cases i
    simp [eval_valleyNet, valleyValue_at_midPoint]
  have hzero_mem : (0 : Real) ∈ proj 0 (reach (valleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by -- 0 ∈ f₂ (conv (f(X))) projected on the first coordiante
    exact ⟨![0], hreach_mid, rfl⟩
    --exact ⟨((fun _ : Fin 1 => (0 : Real)) : Coord 1), hreach_mid, rfl⟩
  have hconv_bddBelow : BddBelow (proj 0 (reach (valleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)))) := by -- f₂ (conv (f(X))) is bounded below.
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    exact exact_valley_nonneg T (le_of_lt hT) z
  have hlb_le_zero : lbproj 0 (reach (valleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) ≤ 0 := by --min f₂ (conv (f(X))) = 0
    simpa [lbproj, proj] using csInf_le hconv_bddBelow hzero_mem
  have hlbP1_le_zero : lbP1 f X 0 ≤ 0 := le_trans hlemma hlb_le_zero
  linarith

theorem theorem33Polytope_upper
    {d : Nat} (X : Polytope (Nat.succ d)) {a b T : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hab : a < b) (hT : 0 < T) :
    ubproj 0 (reach (upperCounterexample (d := d) a b T) X.feasibleSet) + T ≤
      ubP1 (upperCounterexample (d := d) a b T) X 0 := by
  let g := upperCounterexample (d := d) a b T
  let exactSet := proj 0 (reach g X.feasibleSet)
  have hXne : X.feasibleSet.Nonempty := by
    rcases exists_mem_of_firstCoord hproj (by exact ⟨le_rfl, le_of_lt hab⟩) with ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  have hexact_nonempty : exactSet.Nonempty := by
    apply proj_nonempty 0
    exact reach_nonempty g hXne
  have hExact_le : ∀ r ∈ exactSet, r ≤ -T := by
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    rcases hy with ⟨x, hxX, rfl⟩
    have hx0 : x 0 ∈ Set.Icc a b := firstCoord_mem_Icc hproj hxX
    have hnorm : normalized a b (x 0) ∈ Set.Icc (-1 : Real) 1 := normalized_mem_Icc hab hx0
    have hge : T ≤ valleyValue T (prefixPoint (normalized a b (x 0))) :=
      valleyValue_prefix_ge T (normalized a b (x 0)) hT hnorm
    have hneg : -valleyValue T (prefixPoint (normalized a b (x 0))) ≤ -T := by
      linarith
    simpa [g, upperCounterexample, eval_negValleyNet, eval_prefixNet] using hneg
  have hmax_le : ubproj 0 (reach g X.feasibleSet) ≤ -T := by
    simpa [ubproj, exactSet] using csSup_le hexact_nonempty hExact_le
  have hlemma :
      ubproj 0 (reach (negValleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) ≤ ubP1 g X 0 := by
    simpa [g, upperCounterexample] using lemma32Polytope_upper (prefixNet (d := d) a b) (negValleyNet T) X 0 hXne
  have hreach_mid : (((fun _ : Fin 1 => (0 : Real)) : Coord 1)) ∈
      reach (negValleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)) := by
    refine ⟨midPoint, midPoint_mem_convexHull_reach_prefix hproj hab, ?_⟩
    ext i
    fin_cases i
    simp [eval_negValleyNet, valleyValue_at_midPoint]
  have hzero_mem : (0 : Real) ∈
      proj 0 (reach (negValleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by
    exact ⟨((fun _ : Fin 1 => (0 : Real)) : Coord 1), hreach_mid, rfl⟩
  have hconv_bddAbove : BddAbove
      (proj 0 (reach (negValleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet)))) := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    exact exact_negValley_nonpos T (le_of_lt hT) z
  have hzero_le_ub :
      0 ≤ ubproj 0 (reach (negValleyNet T) (convexHull Real (reach (prefixNet (d := d) a b) X.feasibleSet))) := by
    simpa [ubproj, proj] using le_csSup hconv_bddAbove hzero_mem
  have hzero_le_ubP1 : 0 ≤ ubP1 g X 0 := le_trans hzero_le_ub hlemma
  linarith

/-- Polytope version of Theorem 3.3. -/
theorem theorem33Polytope
    {d : Nat} (X : Polytope (Nat.succ d)) {a b T : Real}
    (hproj : (fun x : Coord (Nat.succ d) => x 0) '' X.feasibleSet = Set.Icc a b)
    (hab : a < b) (hT : 0 < T) :
    (∃ f : Net (Nat.succ d) 1,
        lbP1 f X 0 ≤ lbproj 0 (reach f X.feasibleSet) - T) ∧
      (∃ g : Net (Nat.succ d) 1,
        ubproj 0 (reach g X.feasibleSet) + T ≤ ubP1 g X 0) := by
  refine ⟨⟨lowerCounterexample (d := d) a b T, theorem33Polytope_lower X hproj hab hT⟩,
    ⟨upperCounterexample (d := d) a b T, theorem33Polytope_upper X hproj hab hT⟩⟩

end

end Theorem33Polytope

end Net
