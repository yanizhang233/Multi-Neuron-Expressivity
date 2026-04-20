import MultiNeuron.Basic.Polytope
import MultiNeuron.Basic.FunctionGraph
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded

open Set

namespace Net

/-
This file formalizes the layerwise relaxation `P₁`.

The following two results are needed to prove Lemma 3.2:
1. reach_comp_prefix_convex_subset_P1OutputSet_comp:

2. P1OutputSetOnPolytope_bounded:
-/



/-- Auxiliary variables of a network, including all layers. -/
def TraceVar : {n m : Nat} → Net n m → Type
  | n, _, .idLayer _ => Coord n
  | _, m, .affineLayer _ _ => Coord m
  | n, _, .reluLayer _ => Coord n
  | _, _, .comp f g => TraceVar f × TraceVar g

/-- Trace: input variable together with all layer variables. -/
abbrev Trace {n m : Nat} (f : Net n m) := Coord n × TraceVar f

/-- Final output vector read off from a trace. -/
def traceOutput : {n m : Nat} → (f : Net n m) → Trace f → Coord m
  | _, _, .idLayer _, (_, y) => y
  | _, _, .affineLayer _ _, (_, y) => y
  | _, _, .reluLayer _, (_, y) => y
  | _, _, .comp f g, (x, tracevars) =>
      let tf := tracevars.1
      let tg := tracevars.2
      traceOutput g ⟨traceOutput f ⟨x, tf⟩, tg⟩

/-- The exact trace obtained by evaluating the network on a single input. -/
def exactTraceVarSingleInput : {n m : Nat} → (f : Net n m) → Coord n → TraceVar f
  | _, _, .idLayer _, x => x
  | _, _, .affineLayer A b, x => affinemap A b x
  | _, _, .reluLayer _, x => relu x
  | _, _, .comp f g, x => (exactTraceVarSingleInput f x, exactTraceVarSingleInput g (eval f x))

/--on a single input, output induced by the exact trace coincides with the network output. -/
@[simp] theorem traceOutput_exactTraceVarSingleInput {n m : Nat} (f : Net n m) (x : Coord n) :
    traceOutput f (x, exactTraceVarSingleInput f x) = eval f x := by
  induction f with
  | idLayer _ => rfl
  | affineLayer A b => rfl
  | reluLayer _ => rfl
  | comp f g ihf ihg =>
      simp [traceOutput, exactTraceVarSingleInput, ihf, ihg]

/--
P₁ relaxation keeps track of the feasible set through all layers.
- affine layer: the exact function graph
- relu layer: convex hull of the function graph
- composition: glue the suffix trace to the relaxed output set of the prefix.
-/
def P1RelaxedSet : {n m : Nat} → (f : Net n m) → Set (Coord n) → Set (Trace f)
  | n, _, .idLayer _, X =>
      (functionGraph (_root_.id : Coord n → Coord n) X : Set (Trace (.idLayer n)))
  | n, m, .affineLayer A b, X =>
      (functionGraph (affinemap A b) X : Set (Coord n × Coord m))
  | n, _, .reluLayer _, X =>
      (convexHull Real (functionGraph relu X) : Set (Coord n × Coord n))
  | _, _, .comp f g, X =>
      {t | let x := t.1
           let tf := t.2.1
           let tg := t.2.2
           ⟨x, tf⟩ ∈ P1RelaxedSet f X ∧
             ⟨traceOutput f ⟨x, tf⟩, tg⟩ ∈ P1RelaxedSet g (traceOutput f '' P1RelaxedSet f X)}

/-- Output set obtained by P₁:  projecting the trace to the last layer. -/
def P1OutputSet {n m : Nat} (f : Net n m) (X : Set (Coord n)) : Set (Coord m) :=
  traceOutput f '' P1RelaxedSet f X

/-- On idLayer, the output set returned by P₁ is the input set -/
@[simp] theorem P1OutputSet_id {n : Nat} (X : Set (Coord n)) :
    P1OutputSet (Net.idLayer n) X = X := by
  calc
    P1OutputSet (Net.idLayer n) X
        = Prod.snd '' functionGraph (_root_.id : Coord n → Coord n) X := by rfl
    _ = (_root_.id : Coord n → Coord n) '' X :=
          snd_image_functionGraph (_root_.id : Coord n → Coord n) X
    _ = X := by simp

/-- On affineLayer, the output set returned by P₁ is the exact output set-/
@[simp] theorem P1OutputSet_affine {n m : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (b : Coord m) (X : Set (Coord n)) :
    P1OutputSet (Net.affineLayer A b) X = affinemap A b '' X := by
  calc
    P1OutputSet (Net.affineLayer A b) X
        = Prod.snd '' functionGraph (affinemap A b) X := by rfl
    _ = affinemap A b '' X := snd_image_functionGraph (affinemap A b) X

/--On ReLU layer, the output set returned by P₁ is the convex hull of the image of relu(X), where X is input set-/
@[simp] theorem P1OutputSet_relu {n : Nat} (X : Set (Coord n)) :
    P1OutputSet (Net.reluLayer n) X = convexHull Real (relu '' X) := by
  calc
    P1OutputSet (Net.reluLayer n) X
        = Prod.snd '' convexHull Real (functionGraph relu X) := by rfl
    _ = convexHull Real (relu '' X) := snd_image_convexHull_functionGraph relu X

/-the following three theorems are to make proofs cleaner-/
@[simp] theorem mem_P1RelaxedSet_id {n : Nat} (X : Set (Coord n)) (x y : Coord n) :
    (x, y) ∈ P1RelaxedSet (Net.idLayer n) X ↔ x ∈ X ∧ y = x := by
  exact mem_functionGraph (_root_.id : Coord n → Coord n) X x y

@[simp] theorem mem_P1RelaxedSet_affine {n m : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (b : Coord m) (X : Set (Coord n))
    (x : Coord n) (y : Coord m) :
    (x, y) ∈ P1RelaxedSet (Net.affineLayer A b) X ↔ x ∈ X ∧ y = affinemap A b x := by
  exact mem_functionGraph (affinemap A b : Coord n → Coord m) X x y

@[simp] theorem mem_P1RelaxedSet_comp {n m k : Nat}
    (f : Net n m) (g : Net m k) (x : Coord n) (tf : TraceVar f) (tg : TraceVar g)
    (X : Set (Coord n)) :
    (x, (tf, tg)) ∈ P1RelaxedSet (Net.comp f g) X ↔
      (x, tf) ∈ P1RelaxedSet f X ∧
      (traceOutput f (x, tf), tg) ∈ P1RelaxedSet g (P1OutputSet f X) := by
  rfl

/-- all exact trace variables are included, need this theorem to prove theorem reach_subset_P1OutputSet -/
theorem exactTrace_mem_P1RelaxedSet_of_mem {n m : Nat} (f : Net n m) {X : Set (Coord n)}
    {x : Coord n} (hx : x ∈ X) :
    (x, exactTraceVarSingleInput f x) ∈ P1RelaxedSet f X := by
  induction f with
  | idLayer _ =>
      exact (mem_P1RelaxedSet_id X x x).2 ⟨hx, rfl⟩
  | affineLayer A b =>
      exact (mem_P1RelaxedSet_affine A b X x (affinemap A b x)).2 ⟨hx, rfl⟩
  | reluLayer _ =>
      refine subset_convexHull Real (functionGraph relu X) ?_
      exact (mem_functionGraph (f := relu) X x (relu x)).2 ⟨hx, rfl⟩
  | comp f g ihf ihg =>
      change
        (x, exactTraceVarSingleInput f x) ∈ P1RelaxedSet f X ∧
          (traceOutput f (x, exactTraceVarSingleInput f x), exactTraceVarSingleInput g (eval f x)) ∈
            P1RelaxedSet g (P1OutputSet f X)
      refine ⟨ihf hx, ?_⟩
      have hy : eval f x ∈ P1OutputSet f X := by
        exact ⟨(x, exactTraceVarSingleInput f x), ihf hx, traceOutput_exactTraceVarSingleInput f x⟩
      simpa [traceOutput_exactTraceVarSingleInput] using ihg hy

-- /-- P₁ is sound: -/
-- theorem P1Sound {n m : Nat} (f : Net n m) (x : Coord n) :
--     (x, exactTraceVarSingleInput f x) ∈ P1RelaxedSet f ({x} : Set (Coord n)) :=
--   exactTrace_mem_P1RelaxedSet_of_mem f (by simp)

/-- P₁ is sound: the exact reachable set is subset of `P₁` output set. -/
theorem reach_subset_P1OutputSet {n m : Nat} (f : Net n m) (X : Set (Coord n)) :
    reach f X ⊆ P1OutputSet f X := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨(x, exactTraceVarSingleInput f x), exactTrace_mem_P1RelaxedSet_of_mem f hx,
    traceOutput_exactTraceVarSingleInput f x⟩

/-- if X is convex, then projecting P1RelaxedSet onto the input coordinate stays in X. In other words, P₁ does not expand the input set. -/
theorem traceInput_mem_of_mem_P1RelaxedSet {n m : Nat} (f : Net n m) {X : Set (Coord n)}
    (hX : Convex Real X) {x : Coord n} {tf : TraceVar f}
    (h : (x, tf) ∈ P1RelaxedSet f X) :
    x ∈ X := by
  induction f with
  | idLayer _ =>
      exact (mem_P1RelaxedSet_id X x tf).1 h |>.1
  | affineLayer A b =>
      exact (mem_P1RelaxedSet_affine A b X x tf).1 h |>.1
  | reluLayer _ =>
      have hx : x ∈ Prod.fst '' convexHull Real (functionGraph relu X) := ⟨(x, tf), h, rfl⟩
      rw [fst_image_convexHull_functionGraph relu X] at hx
      exact (convexHull_min (subset_rfl) hX) hx
  | comp f g ihf ihg =>
      exact ihf hX h.1


/--
For a composed network f ∘ g, if (P1OutputSet f X) is convex, then ..
-/
theorem P1OutputSet_comp_of_convex {n m k : Nat} (f : Net n m) (g : Net m k) {X : Set (Coord n)}
    (hPrefConv : Convex Real (P1OutputSet f X)) :
    P1OutputSet (Net.comp f g) X = P1OutputSet g (P1OutputSet f X) := by
  ext y
  constructor
  · rintro ⟨⟨x, tf, tg⟩, ht, rfl⟩
    exact ⟨(traceOutput f (x, tf), tg), ht.2, rfl⟩
  · rintro ⟨⟨v, tg⟩, hvg, rfl⟩
    have hv : v ∈ P1OutputSet f X :=
      traceInput_mem_of_mem_P1RelaxedSet g hPrefConv hvg
    rcases hv with ⟨⟨x, tf⟩, htf, rfl⟩
    refine ⟨(x, (tf, tg)), ?_, rfl⟩
    exact (mem_P1RelaxedSet_comp f g x tf tg X).2 ⟨htf, hvg⟩

/-- if input set X is convex, then (P1OutputSet f X) is convex. -/
theorem P1OutputSet_convex {n m : Nat} (f : Net n m) {X : Set (Coord n)} (hX : Convex Real X) :
    Convex Real (P1OutputSet f X) := by
  induction f with
  | idLayer _ =>
      simpa using hX
  | affineLayer A b =>
      simpa using (hX.affine_image (affineLayerMap A b))
  | reluLayer _ =>
      simpa using (convex_convexHull Real (relu '' X))
  | comp f g ihf ihg =>
      have hPrefConv : Convex Real (P1OutputSet f X) := ihf hX
      rw [P1OutputSet_comp_of_convex f g hPrefConv]
      exact ihg hPrefConv



/-- if input set is X, then (P1OutputSet f X) contains convex hull of the reachable set. -/
theorem convex_reach_subset_P1OutputSet {n m : Nat} (f : Net n m) {X : Set (Coord n)}
    (hX : Convex Real X) :
    convexHull Real (reach f X) ⊆ P1OutputSet f X := by
  exact convexHull_min (reach_subset_P1OutputSet f X) (P1OutputSet_convex f hX)

/--
For a composed network f₂ ∘ f₁, input set X is convex, then
f₂ (convex hull (f₁ (X))) ⊆ P1OutputSet (f₂ ∘ f₁) X.
-/
theorem reach_comp_convex_subset_P1OutputSet_comp
    {n m k : Nat} (f₁ : Net n m) (f₂ : Net m k) {X : Set (Coord n)} (hX : Convex Real X) :
    reach f₂ (convexHull Real (reach f₁ X)) ⊆ P1OutputSet (Net.comp f₁ f₂) X := by
  have h₁ : reach f₂ (convexHull Real (reach f₁ X)) ⊆ reach f₂ (P1OutputSet f₁ X) :=
    by
      simpa [Net.reach] using image_mono (convex_reach_subset_P1OutputSet f₁ hX)
  have h₂ : reach f₂ (P1OutputSet f₁ X) ⊆ P1OutputSet f₂ (P1OutputSet f₁ X) :=
    reach_subset_P1OutputSet f₂ (P1OutputSet f₁ X)
  exact Set.Subset.trans h₁ (by
    simpa [P1OutputSet_comp_of_convex f₁ f₂ (P1OutputSet_convex f₁ hX)] using h₂)


/-the following statements on boundedness are needed in the proof of theorem 3.3, when taking lower bounds and upper bounds-/
/--f is a continuous function, input set X is bounded, then f(X) is bounded -/
private theorem isBounded_image_of_continuous {n m : Nat} {S : Set (Coord n)}
    {f : Coord n → Coord m} (hf : Continuous f) (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (f '' S) := by
  letI : ProperSpace (Coord n) := FiniteDimensional.proper ℝ (Coord n)
  exact ((hS.isCompact_closure.image hf).isBounded).subset (image_mono subset_closure)

/--input set X is convex and bounded, then (P1OutputSet f X) is bounded.-/
theorem P1OutputSet_bounded {n m : Nat} (f : Net n m) {X : Set (Coord n)}
    (hXconv : Convex Real X) (hXbdd : Bornology.IsBounded X) :
    Bornology.IsBounded (P1OutputSet f X) := by
  induction f with
  | idLayer _ =>
      simpa using hXbdd
  | affineLayer A b =>
      simpa using isBounded_image_of_continuous (continuous_affinemap A b) hXbdd
  | reluLayer _ =>
      have hImg : Bornology.IsBounded (relu '' X) :=
        isBounded_image_of_continuous (continuous_relu : Continuous (relu : Coord _ → Coord _)) hXbdd
      simpa [P1OutputSet_relu] using (isBounded_convexHull).2 hImg
  | comp f g ihf ihg =>
      have hPrefConv : Convex Real (P1OutputSet f X) := P1OutputSet_convex f hXconv
      have hPrefBdd : Bornology.IsBounded (P1OutputSet f X) := ihf hXconv hXbdd
      rw [P1OutputSet_comp_of_convex f g hPrefConv]
      exact ihg hPrefConv hPrefBdd

/-- `P₁` specialized to a polytope input. -/
def P1RelaxedSetOnPolytope {n m : Nat} (f : Net n m) (X : Polytope n) : Set (Trace f) :=
  P1RelaxedSet f X.feasibleSet

/-- Output set obtained by projecting the trace to the last layer. -/
def P1OutputSetOnPolytope {n m : Nat} (f : Net n m) (X : Polytope n) : Set (Coord m) :=
  P1OutputSet f X.feasibleSet



theorem P1OutputSetOnPolytope_bounded {n m : Nat} (f : Net n m) (X : Polytope n) :
    Bornology.IsBounded (P1OutputSetOnPolytope f X) :=
  P1OutputSet_bounded f X.convex_feasibleSet X.isBounded_feasibleSet



end Net
