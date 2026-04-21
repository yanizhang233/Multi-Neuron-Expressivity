import MultiNeuron.Basic.Polytope
import MultiNeuron.Basic.Network
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Module.Convex

open Set

namespace Net

noncomputable section

/-!
This file formalizes the P_r relaxation.
-/

/-- `layerCount f` counts the number of layers. -/
def layerCount : {n m : Nat} → Net n m → Nat
  | _, _, .idLayer _ => 1
  | _, _, .affineLayer _ _ => 1
  | _, _, .reluLayer _ => 1
  | _, _, .comp f g => layerCount f + layerCount g

@[simp] theorem layerCount_id (n : Nat) : layerCount (Net.idLayer n) = 1 := rfl

@[simp] theorem layerCount_affine {n m : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (b : Coord m) :
    layerCount (Net.affineLayer A b) = 1 := rfl

@[simp] theorem layerCount_relu (n : Nat) : layerCount (Net.reluLayer n) = 1 := rfl

@[simp] theorem layerCount_comp {n m k : Nat} (f : Net n m) (g : Net m k) :
    layerCount (Net.comp f g) = layerCount f + layerCount g := rfl

theorem one_le_layerCount : {n m : Nat} → (f : Net n m) → 1 ≤ layerCount f
  | _, _, .idLayer _ => by simp [layerCount]
  | _, _, .affineLayer _ _ => by simp [layerCount]
  | _, _, .reluLayer _ => by simp [layerCount]
  | _, _, .comp f g => by
      exact le_trans (one_le_layerCount f) (Nat.le_add_right _ _)

/-- One-step output relaxation: convex hull of the exact output set. -/
def WholeNetConvexRelax {n m : Nat} (f : Net n m) (X : Set (Coord n)) : Set (Coord m) :=
  convexHull Real (reach f X)

@[simp] theorem WholeNetConvexRelax_eq_convexHull_reach {n m : Nat} (f : Net n m) (X : Set (Coord n)) :
    WholeNetConvexRelax f X = convexHull Real (reach f X) := rfl

/-- Exact outputs are contained in the block relaxation. -/
theorem reach_subset_WholeNetConvexRelax {n m : Nat} (f : Net n m) (X : Set (Coord n)) :
    reach f X ⊆ WholeNetConvexRelax f X := by
  exact subset_convexHull Real (reach f X)

namespace LayerChain

/-- A network flattened into a left-to-right list of layers. -/
inductive T : Nat → Nat → Type where
  | nil (n : Nat) : T n n
  | cons {n m k : Nat} (f : Net n m) (hcount : layerCount f ≤ 1) (rest : T m k) : T n k

/-- Number of layers in the chain. -/
def lengthChain : {n m : Nat} → T n m → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ _ rest => Nat.succ (lengthChain rest)

/-- Append two chains. -/
def appendChain : {n m k : Nat} → T n m → T m k → T n k
  | _, _, _, .nil _, tail => tail
  | _, _, _, .cons f h rest, tail => .cons f h (appendChain rest tail)

@[simp] theorem lengthChain_append {n m k : Nat} (c₁ : T n m) (c₂ : T m k) :
    lengthChain (appendChain c₁ c₂) = lengthChain c₁ + lengthChain c₂ := by
  induction c₁ with
  | nil n =>
      simp [appendChain, lengthChain]
  | cons f h rest ih =>
      simp [appendChain, lengthChain, ih, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm]

@[simp] theorem appendChain_assoc {n m k l : Nat}
    (c₁ : T n m) (c₂ : T m k) (c₃ : T k l) :
    appendChain (appendChain c₁ c₂) c₃ = appendChain c₁ (appendChain c₂ c₃) := by
  induction c₁ with
  | nil n =>
      simp [appendChain]
  | cons f h rest ih =>
      simp [appendChain, ih]

/-- A chain of exactly `k` identity layers. -/
def idChain (n : Nat) : Nat → T n n
  | 0 => .nil n
  | k + 1 => .cons (Net.idLayer n) (by simp [layerCount]) (idChain n k)

@[simp] theorem lengthChain_idChain (n : Nat) : ∀ k, lengthChain (idChain n k) = k
  | 0 => by simp [idChain, lengthChain]
  | k + 1 => by simp [idChain, lengthChain, lengthChain_idChain n k]

/-- Flatten a network into layers. -/
def FlattenNet : {n m : Nat} → Net n m → T n m
  | _, _, .idLayer n => .cons (Net.idLayer n) (by simp [layerCount]) (.nil n)
  | _, _, .affineLayer A b => .cons (Net.affineLayer A b) (by simp [layerCount]) (.nil _)
  | _, _, .reluLayer n => .cons (Net.reluLayer n) (by simp [layerCount]) (.nil n)
  | _, _, .comp f g => appendChain (FlattenNet f) (FlattenNet g)

/-- Recompose a flattened chain into a network. -/
def ChaintoNet : {n m : Nat} → T n m → Net n m
  | n, _, .nil _ => Net.idLayer n
  | _, _, .cons f _ rest => Net.comp f (ChaintoNet rest)

@[simp] theorem eval_ChaintoNet_idChain (n : Nat) : ∀ k,
    eval (ChaintoNet (idChain n k)) = _root_.id
  | 0 => rfl
  | k + 1 => by
      funext x
      simp [idChain, ChaintoNet, eval_ChaintoNet_idChain n k, Net.eval]

@[simp] theorem reach_ChaintoNet_idChain (n : Nat) (k : Nat) (X : Set (Coord n)) :
    reach (ChaintoNet (idChain n k)) X = X := by
  simp [Net.reach, eval_ChaintoNet_idChain]

/-- Take the first few layers of a chain. -/
def CutPrefix : {n m : Nat} → Nat → T n m → Σ mid, T n mid
  | n, _, 0, _ => ⟨n, .nil n⟩
  | n, _, _ + 1, .nil _ => ⟨n, .nil n⟩
  | _, _, k + 1, .cons f h rest =>
      let p := CutPrefix k rest
      ⟨p.1, .cons f h p.2⟩


@[simp] theorem length_ofNet {n m : Nat} (f : Net n m) :
    lengthChain (FlattenNet f) = layerCount f := by
  induction f with
  | idLayer n =>
      simp [FlattenNet, lengthChain, layerCount]
  | affineLayer A b =>
      simp [FlattenNet, lengthChain, layerCount]
  | reluLayer n =>
      simp [FlattenNet, lengthChain, layerCount]
  | comp f g ihf ihg =>
      simp [FlattenNet, layerCount, lengthChain_append, ihf, ihg]

/-delete, this is not used.-/
/--appending two chains is functionally equivalent to composing the network funtions -/
@[simp] theorem eval_append_eq_comp {n m k : Nat} (c₁ : T n m) (c₂ : T m k) :
    eval (ChaintoNet (appendChain c₁ c₂)) = eval (ChaintoNet c₂) ∘ eval (ChaintoNet c₁) := by
  induction c₁ with
  | nil n =>
      funext x
      simp [appendChain, ChaintoNet]
  | cons f h rest ih =>
      funext x
      simp [appendChain, ChaintoNet, ih]

/--flatten a network to a chain, and then revert the chain back to the network, does not change the network function. -/
@[simp] theorem eval_toNet_ofNet {n m : Nat} (f : Net n m) :
    eval (ChaintoNet (FlattenNet f)) = eval f := by
  induction f with
  | idLayer n =>
      funext x
      simp [FlattenNet, ChaintoNet, Net.eval]
  | affineLayer A b =>
      funext x
      simp [FlattenNet, ChaintoNet, Net.eval]
  | reluLayer n =>
      funext x
      simp [FlattenNet, ChaintoNet, Net.eval]
  | comp f g ihf ihg =>
      funext x
      simp [FlattenNet, Net.eval, ihf, ihg]

/--appending an id layer does not change the network function-/
@[simp] theorem eval_ChaintoNet_append_idChain {n m : Nat}
    (c : T n m) (r : Nat) :
    eval (ChaintoNet (appendChain c (idChain m r))) = eval (ChaintoNet c) := by
  funext x
  simp [eval_append_eq_comp, eval_ChaintoNet_idChain, Function.comp]

/--appending an id layer does not change the reachable set of a network-/
@[simp] theorem reach_ChaintoNet_append_idChain {n m : Nat}
    (c : T n m) (r : Nat) (X : Set (Coord n)) :
    reach (ChaintoNet (appendChain c (idChain m r))) X = reach (ChaintoNet c) X := by
  simp [Net.reach]

end LayerChain

/--
`FullTrace c` stores all variables along a flattened chain `c`.

For a chain of length `L`, this type is the nested product
`(v⁽⁰⁾, (v⁽¹⁾, ... (v⁽ᴸ⁻¹⁾, v⁽ᴸ⁾)...))`.
-/
abbrev FullTrace : {n m : Nat} → LayerChain.T n m → Type
  | n, _, .nil _ => Coord n
  | n, _, .cons _ _ rest => Coord n × FullTrace rest

/--need this because full trace is used as the ambient space of a convexHull, and convexHull only makes sense in a type with additive structure.-/
instance instAddCommMonoidFullTrace :
    {n m : Nat} → (c : LayerChain.T n m) → AddCommMonoid (FullTrace c)
  | _, _, .nil _ => by
      simpa [FullTrace, Coord] using (inferInstance : AddCommMonoid (Fin _ → Real))
  | _, _, .cons _ _ rest => by
      let _ := instAddCommMonoidFullTrace rest
      simpa [FullTrace, Coord] using (inferInstance : AddCommMonoid ((Fin _ → Real) × FullTrace rest))

instance instModuleFullTrace :
    {n m : Nat} → (c : LayerChain.T n m) → Module Real (FullTrace c)
  | _, _, .nil _ => by
      simpa [FullTrace, Coord] using (inferInstance : Module Real (Fin _ → Real))
  | _, _, .cons _ _ rest => by
      let _ := instAddCommMonoidFullTrace rest
      let _ := instModuleFullTrace rest
      simpa [FullTrace, Coord] using (inferInstance : Module Real ((Fin _ → Real) × FullTrace rest))

instance instTopologicalSpaceFullTrace :
    {n m : Nat} → (c : LayerChain.T n m) → TopologicalSpace (FullTrace c)
  | _, _, .nil _ => by
      simpa [FullTrace, Coord] using (inferInstance : TopologicalSpace (Fin _ → Real))
  | _, _, .cons _ _ rest => by
      let _ := instTopologicalSpaceFullTrace rest
      simpa [FullTrace, Coord] using
        (inferInstance : TopologicalSpace ((Fin _ → Real) × FullTrace rest))


/-- reading off input variable `v⁽⁰⁾` of a full trace. -/
def traceInput : {n m : Nat} → {c : LayerChain.T n m} → FullTrace c → Coord n
  | _, _, .nil _, x => x
  | _, _, .cons _ _ _, t => t.1

/-- reading off final output variable of a full trace. -/
def traceOutput : {n m : Nat} → {c : LayerChain.T n m} → FullTrace c → Coord m
  | _, _, .nil _, x => x
  | _, _, .cons _ _ _, t => traceOutput t.2

/-- Suffix trace starting at layer 2. -/
def dropFstLayerTrace {n m k : Nat} {f : Net n m} {hcount : layerCount f ≤ 1}
    {rest : LayerChain.T m k} :
    FullTrace (.cons f hcount rest) → FullTrace rest
  | t => t.2

/-- The exact full trace evaluated at a single input. -/
def exactTraceSingleInput :
    {n m : Nat} → (c : LayerChain.T n m) → Coord n → FullTrace c
  | _, _, .nil _, x => x
  | _, _, .cons f _ rest, x =>
      show Coord _ × FullTrace rest from (x, exactTraceSingleInput rest (eval f x))

/--the full trace is continuous-/
theorem continuous_exactTraceSingleInput :
    {n m : Nat} → (c : LayerChain.T n m) → Continuous (exactTraceSingleInput c)
  | _, _, .nil _ => by
      simpa [exactTraceSingleInput] using (continuous_id : Continuous (fun x : Coord _ => x))
  | _, _, .cons f _ rest => by
      change Continuous (fun x => (x, exactTraceSingleInput rest (eval f x)))
      exact (continuous_id : Continuous (fun x : Coord _ => x)).prodMk
        ((continuous_exactTraceSingleInput rest).comp (Net.continuous_eval f))

/-- The exact full trace evaluated at an input set. -/
def exactTraceSet {n m : Nat} (c : LayerChain.T n m) (X : Set (Coord n)) : Set (FullTrace c) :=
  exactTraceSingleInput c '' X

/--
the convex hull of the exact full trace set on the input set.
-/
def convHullTrace {n m : Nat} (c : LayerChain.T n m) (X : Set (Coord n)) : Set (FullTrace c) :=
  convexHull Real (exactTraceSet c X)

theorem continuous_traceOutput :
    {n m : Nat} → (c : LayerChain.T n m) → Continuous (@traceOutput n m c)
  | _, _, .nil _ => by
      simpa [traceOutput] using (continuous_id : Continuous (fun x : Coord _ => x))
  | _, _, .cons _ _ rest => by
      simpa [traceOutput] using (continuous_traceOutput rest).comp continuous_snd

/-- First `k` variables of a full trace. -/
def CutPrefixTrace : {n m : Nat} → (k : Nat) → (c : LayerChain.T n m) →
    FullTrace c → FullTrace (LayerChain.CutPrefix k c).2
  | _, _, 0, _, t => traceInput t
  | _, _, _ + 1, .nil _, t => traceInput t
  | _, _, k + 1, .cons _ _ rest, t =>
      show Coord _ × FullTrace (LayerChain.CutPrefix k rest).2 from (t.1, CutPrefixTrace k rest t.2)

-- @[simp] theorem traceInput_exactTraceSingleInput {n m : Nat}
--     (c : LayerChain.T n m) (x : Coord n) :
--     traceInput (exactTraceSingleInput c x) = x := by
--   induction c with
--   | nil n =>
--       rfl
--   | cons f h rest ih =>
--       rfl

@[simp] theorem traceOutput_exactTraceSingleInput {n m : Nat}
    (c : LayerChain.T n m) (x : Coord n) :
    traceOutput (exactTraceSingleInput c x) = eval (LayerChain.ChaintoNet c) x := by
  induction c with
  | nil n =>
      rfl
  | cons f h rest ih =>
      simpa [exactTraceSingleInput, traceOutput, LayerChain.ChaintoNet, Net.eval] using
        ih (eval f x)

@[simp] theorem traceTake_exactTraceSingleInput :
    {n m : Nat} → (k : Nat) → (c : LayerChain.T n m) → (x : Coord n) →
      CutPrefixTrace k c (exactTraceSingleInput c x) =
        exactTraceSingleInput (LayerChain.CutPrefix k c).2 x
  | n, _, 0, c, x => by
      cases c <;> rfl
  | n, _, _ + 1, .nil _, x => by
      rfl
  | _, _, k + 1, .cons f h rest, x => by
      simp [CutPrefixTrace, LayerChain.CutPrefix, exactTraceSingleInput, traceTake_exactTraceSingleInput]

namespace LayerChain

/-- Splice two compatible traces into a trace of the appended chain. -/
def spliceTrace :
    {n m k : Nat} → {c₁ : T n m} → {c₂ : T m k} →
      FullTrace c₁ → FullTrace c₂ → FullTrace (appendChain c₁ c₂)
  | _, _, _, .nil _, _, _u, v => v
  | _, _, _, .cons _ _ rest, _, u, v =>
      show Coord _ × FullTrace (appendChain rest _)
      from (u.1, spliceTrace u.2 v)

@[simp] theorem traceOutput_spliceTrace
    {n m k : Nat} {c₁ : T n m} {c₂ : T m k}
    (u : FullTrace c₁) (v : FullTrace c₂) :
    traceOutput (spliceTrace u v) = traceOutput v := by
  induction c₁ generalizing k with
  | nil n =>
      rfl
  | cons f h rest ih =>
      simpa [spliceTrace, traceOutput] using ih u.2 v

theorem CutPrefix_append_eq_of_le_length
    {n m k : Nat} (p : Nat) (c₁ : T n m) (c₂ : T m k)
    (h : p ≤ lengthChain c₁) :
    CutPrefix p (appendChain c₁ c₂) = CutPrefix p c₁ := by
  induction p generalizing n m k c₁ c₂ with
  | zero =>
      cases c₁ <;> simp [CutPrefix]
  | succ p ih =>
      cases c₁ with
      | nil n =>
          cases h
      | cons f hcount rest =>
          simp [CutPrefix, appendChain]
          rw [ih rest c₂ (Nat.le_of_succ_le_succ h)]
          constructor <;> rfl

/-- Linear map corresponding to reading off the final output coordinate of a full trace. -/
def traceOutputLinear : {n m : Nat} → (c : T n m) → FullTrace c →ₗ[ℝ] Coord m
  | _, _, .nil _ => by
      simpa [FullTrace] using (LinearMap.id : Coord _ →ₗ[ℝ] Coord _)
  | _, _, .cons _ _ rest =>
      (traceOutputLinear rest).comp (LinearMap.snd ℝ (Coord _) (FullTrace rest))

@[simp] theorem traceOutputLinear_apply {n m : Nat}
    (c : T n m) (t : FullTrace c) :
    traceOutputLinear c t = traceOutput t := by
  induction c with
  | nil n =>
      change ((LinearMap.id : Coord n →ₗ[ℝ] Coord n) t) = t
      simp
  | cons f h rest ih =>
      cases t with
      | mk fst snd =>
          simpa [traceOutputLinear, traceOutput] using ih snd

@[simp] theorem traceOutputLinear_image_exactTraceSet {n m : Nat}
    (c : T n m) (X : Set (Coord n)) :
    traceOutputLinear c '' exactTraceSet c X = reach (ChaintoNet c) X := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases ht with ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨exactTraceSingleInput c x, ⟨x, hx, rfl⟩, by
      simp⟩

/-- Projecting the convex hull of exact traces to the final output yields the convexified reachable set. -/
theorem traceOutput_image_convHullTrace {n m : Nat}
    (c : T n m) (X : Set (Coord n)) :
    traceOutput '' convHullTrace c X = WholeNetConvexRelax (ChaintoNet c) X := by
  calc
    traceOutput '' convHullTrace c X
        = traceOutputLinear c '' convHullTrace c X := by
            ext y
            constructor <;> rintro ⟨t, ht, rfl⟩ <;> exact ⟨t, ht, by simp⟩
    _ = convexHull Real (traceOutputLinear c '' exactTraceSet c X) := by
          simpa [convHullTrace] using
            (traceOutputLinear c).image_convexHull (exactTraceSet c X)
    _ = convexHull Real (reach (ChaintoNet c) X) := by
          rw [traceOutputLinear_image_exactTraceSet]
    _ = WholeNetConvexRelax (ChaintoNet c) X := by
          rw [WholeNetConvexRelax_eq_convexHull_reach]

/-- Linear map reading off the first `k` variables of a full trace. -/
def CutPrefixTraceLinear :
    {n m : Nat} → (k : Nat) → (c : T n m) →
      FullTrace c →ₗ[ℝ] FullTrace (CutPrefix k c).2
  | _, _, 0, .nil _ => by
      simpa [CutPrefix, FullTrace] using (LinearMap.id : Coord _ →ₗ[ℝ] Coord _)
  | _, _, 0, .cons _ _ rest =>
      LinearMap.fst ℝ (Coord _) (FullTrace rest)
  | _, _, _ + 1, .nil _ => by
      simpa [CutPrefix, FullTrace] using (LinearMap.id : Coord _ →ₗ[ℝ] Coord _)
  | _, _, k + 1, .cons _ _ rest =>
      (LinearMap.fst ℝ (Coord _) (FullTrace rest)).prod
        ((CutPrefixTraceLinear k rest).comp (LinearMap.snd ℝ (Coord _) (FullTrace rest)))

@[simp] theorem CutPrefixTraceLinear_apply {n m : Nat}
    (k : Nat) (c : T n m) (t : FullTrace c) :
    CutPrefixTraceLinear k c t = CutPrefixTrace k c t := by
  induction k generalizing n m c with
  | zero =>
      cases c with
      | nil n =>
          rfl
      | cons f h rest =>
          cases t
          rfl
  | succ k ih =>
      cases c with
      | nil n =>
          rfl
      | cons f h rest =>
          cases t with
          | mk fst snd =>
              have hs : CutPrefixTraceLinear k rest snd = CutPrefixTrace k rest snd := ih rest snd
              change (fst, CutPrefixTraceLinear k rest snd) = (fst, CutPrefixTrace k rest snd)
              rw [hs]

@[simp] theorem CutPrefixTraceLinear_image_exactTraceSet {n m : Nat}
    (k : Nat) (c : T n m) (X : Set (Coord n)) :
    CutPrefixTraceLinear k c '' exactTraceSet c X =
      exactTraceSet (CutPrefix k c).2 X := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases ht with ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simpa [CutPrefixTraceLinear_apply] using
      traceTake_exactTraceSingleInput k c x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨exactTraceSingleInput c x, ⟨x, hx, rfl⟩, by
      simpa [CutPrefixTraceLinear_apply] using traceTake_exactTraceSingleInput k c x⟩

theorem CutPrefixTrace_mem_convHullTrace_of_mem
    {n m : Nat} (k : Nat) (c : T n m) {X : Set (Coord n)} {t : FullTrace c}
    (ht : t ∈ convHullTrace c X) :
    CutPrefixTrace k c t ∈ convHullTrace (CutPrefix k c).2 X := by
  let L := CutPrefixTraceLinear k c
  have hImage :
      L '' convHullTrace c X = convexHull Real (L '' exactTraceSet c X) := by
    simpa [convHullTrace] using L.image_convexHull (exactTraceSet c X)
  have hLt : L t ∈ L '' convHullTrace c X := ⟨t, ht, rfl⟩
  rw [hImage, CutPrefixTraceLinear_image_exactTraceSet] at hLt
  simpa [L, CutPrefixTraceLinear_apply, convHullTrace] using hLt

theorem dropFstLayerTrace_mem_convHullTrace_of_mem
    {n m k : Nat} {f : Net n m} {hcount : layerCount f ≤ 1}
    {rest : T m k} {X : Set (Coord n)}
    {t : FullTrace (.cons f hcount rest)}
    (ht : t ∈ convHullTrace (.cons f hcount rest) X) :
    dropFstLayerTrace t ∈ convHullTrace rest (WholeNetConvexRelax f X) := by
  let L : FullTrace (.cons f hcount rest) →ₗ[ℝ] FullTrace rest :=
    LinearMap.snd ℝ (Coord n) (FullTrace rest)
  have hImage :
      L '' convHullTrace (.cons f hcount rest) X =
        convexHull Real (L '' exactTraceSet (.cons f hcount rest) X) := by
    simpa [convHullTrace] using L.image_convexHull (exactTraceSet (.cons f hcount rest) X)
  have hLt : L t ∈ L '' convHullTrace (.cons f hcount rest) X := ⟨t, ht, rfl⟩
  rw [hImage] at hLt
  have hExact :
      L '' exactTraceSet (.cons f hcount rest) X = exactTraceSet rest (reach f X) := by
    ext u
    constructor
    · rintro ⟨t', ht', rfl⟩
      rcases ht' with ⟨x, hx, rfl⟩
      refine ⟨eval f x, ⟨x, hx, rfl⟩, ?_⟩
      simp [L, exactTraceSingleInput]
    · rintro ⟨y, ⟨x, hx, rfl⟩, hu⟩
      refine ⟨exactTraceSingleInput (.cons f hcount rest) x, ⟨x, hx, rfl⟩, ?_⟩
      simpa [L, dropFstLayerTrace, exactTraceSingleInput] using hu
  rw [hExact] at hLt
  exact (convexHull_mono (image_mono (reach_subset_WholeNetConvexRelax f X))) hLt

end LayerChain

/-- Exact traces are contained in the relaxation. -/
theorem exactTrace_mem_RelaxedSet_of_mem {n m : Nat}
    (c : LayerChain.T n m) {X : Set (Coord n)} {x : Coord n} (hx : x ∈ X) :
    exactTraceSingleInput c x ∈ convHullTrace c X := by
  exact subset_convexHull Real (exactTraceSet c X) ⟨x, hx, rfl⟩

/--
sliding-window cross-layer relaxation on a flattened chain.
If the remaining suffix has at most `r` layers, relax it in one shot.
Otherwise:
1. process the first `r` consecutive layers by their exact convex hull;
2. recurse on the suffix starting from layer 2, with input set equal to the
   projection of the first local window to `v⁽¹⁾`, i.e. `WholeNetConvexRelax` of the
   first layer.
-/
def PrRelaxedSetChain (r : Nat) (hr : 0 < r) :
    {n m : Nat} → (c : LayerChain.T n m) → Set (Coord n) → Set (FullTrace c)
  | _, _, .nil n, X => convHullTrace (.nil n) X
  | _, _, .cons f hcount rest, X =>
      let c : LayerChain.T _ _ := .cons f hcount rest
      if _hlen : LayerChain.lengthChain c ≤ r then
        convHullTrace c X
      else
        let pref := (LayerChain.CutPrefix r c).2
        {t | CutPrefixTrace r c t ∈ convHullTrace pref X ∧
            dropFstLayerTrace t ∈ PrRelaxedSetChain r hr rest (WholeNetConvexRelax f X)}
termination_by n m c _ => LayerChain.lengthChain c
decreasing_by
  simp [LayerChain.lengthChain]

/-- Output set obtained by projecting the relaxed full trace to the last variable, i.e., the feasible output set returned by P_r. -/
def PrOutputSetChain {r n m : Nat}
    (hr : 0 < r) (c : LayerChain.T n m) (X : Set (Coord n)) : Set (Coord m) :=
  traceOutput '' PrRelaxedSetChain r hr c X

/-- P_r is sound: exact traces are contained in the sliding-window relaxation. -/
theorem exactTrace_mem_PrRelaxedSetChain_of_mem
    (r : Nat) (hr : 0 < r) :
    {n m : Nat} → (c : LayerChain.T n m) → {X : Set (Coord n)} → {x : Coord n} →
      x ∈ X → exactTraceSingleInput c x ∈ PrRelaxedSetChain r hr c X
  | _, _, .nil n, _, x, hx => by
      simpa [PrRelaxedSetChain] using
        exactTrace_mem_RelaxedSet_of_mem (.nil n) hx
  | _, _, .cons f hcount rest, X, x, hx => by
      let c : LayerChain.T _ _ := .cons f hcount rest
      by_cases hlen : LayerChain.lengthChain c ≤ r
      · simpa [PrRelaxedSetChain, c, hlen] using
          exactTrace_mem_RelaxedSet_of_mem c hx
      · simp [PrRelaxedSetChain, c, hlen]
        refine ⟨?_, ?_⟩
        · simpa [c, traceTake_exactTraceSingleInput] using
            exactTrace_mem_RelaxedSet_of_mem ((LayerChain.CutPrefix r c).2) hx
        · have hy : eval f x ∈ WholeNetConvexRelax f X := by
            exact reach_subset_WholeNetConvexRelax f X ⟨x, hx, rfl⟩
          simpa [dropFstLayerTrace, exactTraceSingleInput] using
            exactTrace_mem_PrRelaxedSetChain_of_mem r hr rest hy


theorem reach_toNet_subset_PrOutputSetChain
    (r : Nat) (hr : 0 < r) {n m : Nat} (c : LayerChain.T n m) (X : Set (Coord n)) :
    reach (LayerChain.ChaintoNet c) X ⊆ PrOutputSetChain hr c X := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨exactTraceSingleInput c x, exactTrace_mem_PrRelaxedSetChain_of_mem r hr c hx, ?_⟩
  exact traceOutput_exactTraceSingleInput c x

theorem PrRelaxedSetChain_eq_convHullTrace_of_lengthChain_le
    {r n m : Nat} (hr : 0 < r) (c : LayerChain.T n m) (X : Set (Coord n))
    (hlen : LayerChain.lengthChain c ≤ r) :
    PrRelaxedSetChain r hr c X = convHullTrace c X := by
  cases c with
  | nil n =>
      simp [PrRelaxedSetChain, convHullTrace]
  | cons f hcount rest =>
      simp [PrRelaxedSetChain, hlen]

/-- definition of P_r: sliding-window relaxed trace set for a network. -/
def PrRelaxedSet {r n m : Nat}
    (hr : 0 < r) (f : Net n m) (X : Set (Coord n)) :
    Set (FullTrace (LayerChain.FlattenNet f)) :=
  PrRelaxedSetChain r hr (LayerChain.FlattenNet f) X

/--feasible output set for a network induced by Pr. -/
def PrOutputSet {r n m : Nat}
    (hr : 0 < r) (f : Net n m) (X : Set (Coord n)) : Set (Coord m) :=
  PrOutputSetChain hr (LayerChain.FlattenNet f) X

/-- P_r on a polytope input. -/
def PrOutputSetOnPolytope {r n m : Nat}
    (hr : 0 < r) (f : Net n m) (X : Polytope n) : Set (Coord m) :=
  PrOutputSet hr f X.feasibleSet

/-- Pr is sound: feasible output set for a network induced by Pr is a superset of the exact reachable set. -/
theorem reach_subset_PrOutputSet {r n m : Nat}
    (hr : 0 < r) (f : Net n m) (X : Set (Coord n)) :
    reach f X ⊆ PrOutputSet hr f X := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨exactTraceSingleInput (LayerChain.FlattenNet f) x,
    exactTrace_mem_PrRelaxedSetChain_of_mem r hr (LayerChain.FlattenNet f) hx, ?_⟩
  rw [traceOutput_exactTraceSingleInput, LayerChain.eval_toNet_ofNet]

/-- Prepend exactly some identity layers in front of a network. -/
def prependIds {n m : Nat} : Nat → Net n m → Net n m
  | 0, f => f
  | k + 1, f => Net.comp (Net.idLayer n) (prependIds k f)

@[simp] theorem layerCount_prependIds {n m : Nat} :
    ∀ k (f : Net n m), layerCount (prependIds k f) = k + layerCount f
  | 0, f => by simp [prependIds]
  | k + 1, f => by
      rw [prependIds, layerCount_comp, layerCount_id, layerCount_prependIds k f]
      omega

@[simp] theorem eval_prependIds {n m : Nat} :
    ∀ k (f : Net n m), eval (prependIds k f) = eval f
  | 0, f => rfl
  | k + 1, f => by
      funext x
      simp [prependIds, eval_prependIds k f, Net.eval]

@[simp] theorem reach_prependIds {n m : Nat}
    (k : Nat) (f : Net n m) (X : Set (Coord n)) :
    reach (prependIds k f) X = reach f X := by
  simp [Net.reach, eval_prependIds]

@[simp] theorem FlattenNet_prependIds {n m : Nat} :
    ∀ k (f : Net n m),
      LayerChain.FlattenNet (prependIds k f) =
        LayerChain.appendChain (LayerChain.idChain n k) (LayerChain.FlattenNet f)
  | 0, f => by simp [prependIds, LayerChain.idChain, LayerChain.appendChain]
  | k + 1, f => by
      calc
        LayerChain.FlattenNet (prependIds (k + 1) f)
            = LayerChain.appendChain (LayerChain.FlattenNet (Net.idLayer n))
                (LayerChain.FlattenNet (prependIds k f)) := by
                  simp [prependIds, LayerChain.FlattenNet]
        _ = LayerChain.appendChain (LayerChain.FlattenNet (Net.idLayer n))
              (LayerChain.appendChain (LayerChain.idChain n k) (LayerChain.FlattenNet f)) := by
                rw [FlattenNet_prependIds k f]
        _ = LayerChain.T.cons (Net.idLayer n) (by simp [layerCount])
              (LayerChain.appendChain (LayerChain.idChain n k) (LayerChain.FlattenNet f)) := by
                simp [LayerChain.FlattenNet, LayerChain.appendChain]
        _ = LayerChain.appendChain (LayerChain.idChain n (k + 1)) (LayerChain.FlattenNet f) := by
              simp [LayerChain.idChain, LayerChain.appendChain]

@[simp] theorem prependIds_add {n m : Nat} (a b : Nat) (f : Net n m) :
    prependIds a (prependIds b f) = prependIds (a + b) f := by
  induction a with
  | zero =>
      simp [prependIds]
  | succ a ih =>
      simpa [prependIds, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        congrArg (fun g => Net.comp (Net.idLayer n) g) ih

/-- The pumped network obtained by inserting exactly `2 * r` identity layers between `f₁` and `f₂`. -/
def pumpNetPr {d d' k : Nat} (f₁ : Net d d') (f₂ : Net d' k) (r : Nat) : Net d k :=
  Net.comp f₁ (prependIds r (prependIds r f₂))

@[simp] theorem eval_pumpNetPr {d d' k : Nat}
    (f₁ : Net d d') (f₂ : Net d' k) (r : Nat) :
    eval (pumpNetPr f₁ f₂ r) = eval (Net.comp f₁ f₂) := by
  funext x
  simp [pumpNetPr, eval_prependIds, Net.eval]

@[simp] theorem reach_pumpNetPr {d d' k : Nat}
    (f₁ : Net d d') (f₂ : Net d' k) (r : Nat) (X : Set (Coord d)) :
    reach (pumpNetPr f₁ f₂ r) X = reach (Net.comp f₁ f₂) X := by
  simp [Net.reach, eval_pumpNetPr]

@[simp] theorem FlattenNet_pumpNetPr {d d' k : Nat}
    (f₁ : Net d d') (f₂ : Net d' k) (r : Nat) :
    LayerChain.FlattenNet (pumpNetPr f₁ f₂ r) =
      LayerChain.appendChain
        (LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r))
        (LayerChain.appendChain (LayerChain.idChain d' r) (LayerChain.FlattenNet f₂)) := by
  calc
    LayerChain.FlattenNet (pumpNetPr f₁ f₂ r)
        = LayerChain.appendChain (LayerChain.FlattenNet f₁)
            (LayerChain.FlattenNet (prependIds r (prependIds r f₂))) := by
              simp [pumpNetPr, LayerChain.FlattenNet]
    _ = LayerChain.appendChain (LayerChain.FlattenNet f₁)
          (LayerChain.appendChain (LayerChain.idChain d' r)
            (LayerChain.FlattenNet (prependIds r f₂))) := by
              rw [FlattenNet_prependIds]
    _ = LayerChain.appendChain (LayerChain.FlattenNet f₁)
          (LayerChain.appendChain (LayerChain.idChain d' r)
            (LayerChain.appendChain (LayerChain.idChain d' r) (LayerChain.FlattenNet f₂))) := by
              rw [FlattenNet_prependIds]
    _ = LayerChain.appendChain
          (LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r))
          (LayerChain.appendChain (LayerChain.idChain d' r) (LayerChain.FlattenNet f₂)) := by
            rw [LayerChain.appendChain_assoc]

/-- Radius chosen from a total depth `L` by the rule `max(1, floor (α * L))`. -/
noncomputable def alphaRadius (α : Real) (L : Nat) : Nat :=
  max 1 ⌊α * L⌋₊

theorem alphaRadius_pos (α : Real) (L : Nat) : 0 < alphaRadius α L := by
  unfold alphaRadius
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 ⌊α * ↑L⌋₊)

/--
for a net f = f₂ ∘ f₁, through inserting id layers in between f₂ and f₁, we get
reach f₂ (convexHull Real (reach f₁ X)) is a subset of the output set produced by P_r
-/
theorem reach_conv_middle_subset_PrOutputSet_pump_of_glue
    {d d' k : Nat} {r : Nat} (hr : 0 < r)
    (f₁ : Net d d') (f₂ : Net d' k)
    (X : Set (Coord d))
    (hglue :
      let left : LayerChain.T d d' :=
        LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r)
      let right : LayerChain.T d' k :=
        LayerChain.appendChain (LayerChain.idChain d' r) (LayerChain.FlattenNet f₂)
      let whole : LayerChain.T d k := LayerChain.appendChain left right
      ∀ {u : FullTrace left} {v : FullTrace right},
        u ∈ convHullTrace left X →
        v ∈ PrRelaxedSetChain r hr right {traceOutput u} →
        LayerChain.spliceTrace u v ∈ PrRelaxedSetChain r hr whole X) :
    reach f₂ (convexHull Real (reach f₁ X)) ⊆
      PrOutputSet hr (pumpNetPr f₁ f₂ r) X := by
  intro y hy
  change y ∈ PrOutputSetChain hr (LayerChain.FlattenNet (pumpNetPr f₁ f₂ r)) X
  rw [FlattenNet_pumpNetPr]
  let left : LayerChain.T d d' :=
    LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r)
  let right : LayerChain.T d' k :=
    LayerChain.appendChain (LayerChain.idChain d' r) (LayerChain.FlattenNet f₂)
  let whole : LayerChain.T d k := LayerChain.appendChain left right
  rcases hy with ⟨z, hz, rfl⟩
  have hzLeft : z ∈ WholeNetConvexRelax (LayerChain.ChaintoNet left) X := by
    simpa [left, WholeNetConvexRelax_eq_convexHull_reach,
      LayerChain.reach_ChaintoNet_append_idChain, Net.reach,
      LayerChain.eval_toNet_ofNet] using hz
  rw [← LayerChain.traceOutput_image_convHullTrace left X] at hzLeft
  rcases hzLeft with ⟨u, hu, huz⟩
  have hv0 :
      exactTraceSingleInput right z ∈ PrRelaxedSetChain r hr right ({z} : Set (Coord d')) := by
    exact exactTrace_mem_PrRelaxedSetChain_of_mem r hr right (by simp)
  have hv :
      exactTraceSingleInput right z ∈ PrRelaxedSetChain r hr right ({traceOutput u} : Set (Coord d')) := by
    simpa [huz] using hv0
  have hwhole :
      LayerChain.spliceTrace (c₁ := left) (c₂ := right) u (exactTraceSingleInput right z) ∈
        PrRelaxedSetChain r hr whole X := by
    simpa [left, right, whole] using hglue hu hv
  refine ⟨LayerChain.spliceTrace (c₁ := left) (c₂ := right) u (exactTraceSingleInput right z), ?_, ?_⟩
  · simpa [whole] using hwhole
  · rw [LayerChain.traceOutput_spliceTrace]
    simp [right, LayerChain.eval_append_eq_comp, LayerChain.eval_ChaintoNet_idChain,
      LayerChain.eval_toNet_ofNet, Function.comp]

/--
If the inserted identity buffer is at least `r`, then the same gluing argument
can be applied to a larger pumped network by absorbing the extra identities
into the suffix network.
-/
theorem reach_conv_middle_subset_PrOutputSet_pump_of_glue_buffer
    {d d' k : Nat} {r s : Nat} (hr : 0 < r) (hrs : r ≤ s)
    (f₁ : Net d d') (f₂ : Net d' k) (X : Set (Coord d))
    (hglue :
      let f₂' := prependIds (2 * (s - r)) f₂
      let left : LayerChain.T d d' :=
        LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r)
      let right : LayerChain.T d' k :=
        LayerChain.appendChain (LayerChain.idChain d' r) (LayerChain.FlattenNet f₂')
      let whole : LayerChain.T d k := LayerChain.appendChain left right
      ∀ {u : FullTrace left} {v : FullTrace right},
        u ∈ convHullTrace left X →
        v ∈ PrRelaxedSetChain r hr right {traceOutput u} →
        LayerChain.spliceTrace u v ∈ PrRelaxedSetChain r hr whole X) :
    reach f₂ (convexHull Real (reach f₁ X)) ⊆
      PrOutputSet hr (pumpNetPr f₁ f₂ s) X := by
  let f₂' := prependIds (2 * (s - r)) f₂
  have hpump : pumpNetPr f₁ f₂' r = pumpNetPr f₁ f₂ s := by
    have hbuf : r + (r + 2 * (s - r)) = s + s := by
      omega
    calc
      pumpNetPr f₁ f₂' r
          = Net.comp f₁ (prependIds (r + (r + 2 * (s - r))) f₂) := by
              simp [pumpNetPr, f₂', prependIds_add]
      _ = Net.comp f₁ (prependIds (s + s) f₂) := by rw [hbuf]
      _ = pumpNetPr f₁ f₂ s := by
            simp [pumpNetPr, prependIds_add]
  have hreach :
      reach f₂' (convexHull Real (reach f₁ X)) =
        reach f₂ (convexHull Real (reach f₁ X)) := by
    simp [f₂', reach_prependIds]
  have hglue' :
      ∀ {u :
          FullTrace
            (LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r))}
        {v :
          FullTrace
            (LayerChain.appendChain (LayerChain.idChain d' r) (LayerChain.FlattenNet f₂'))},
        u ∈ convHullTrace
            (LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r)) X →
        v ∈ PrRelaxedSetChain r hr
            (LayerChain.appendChain (LayerChain.idChain d' r) (LayerChain.FlattenNet f₂'))
            {traceOutput u} →
        LayerChain.spliceTrace u v ∈
          PrRelaxedSetChain r hr
            (LayerChain.appendChain
              (LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r))
              (LayerChain.appendChain (LayerChain.idChain d' r) (LayerChain.FlattenNet f₂')))
            X := by
    intro u v hu hv
    exact hglue hu hv
  rw [← hreach, ← hpump]
  exact reach_conv_middle_subset_PrOutputSet_pump_of_glue hr f₁ f₂' X hglue'

/--
Choose the sliding-window radius from the total depth `L` of a pumped network by
`r = max(1, floor (α * L))`.
If the pumped network is deep enough that this chosen radius fits inside the
inserted identity buffer, then the middle-convexified reachable set is
contained in the `P_r` output set of that pumped network.
-/
theorem reach_conv_middle_subset_PrOutputSet_pump_of_glue_radius
    {d d' k : Nat} (α : Real) (_hα : α < 1)
    (f₁ : Net d d') (f₂ : Net d' k) (s : Nat) (X : Set (Coord d))
    (hlarge :
      let r := alphaRadius α (layerCount (pumpNetPr f₁ f₂ s))
      r ≤ s)
    (hglue :
      let r := alphaRadius α (layerCount (pumpNetPr f₁ f₂ s))
      let hr : 0 < r := alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s))
      let f₂' := prependIds (2 * (s - r)) f₂
      let left : LayerChain.T d d' :=
        LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r)
      let right : LayerChain.T d' k :=
        LayerChain.appendChain (LayerChain.idChain d' r) (LayerChain.FlattenNet f₂')
      let whole : LayerChain.T d k := LayerChain.appendChain left right
      ∀ {u : FullTrace left} {v : FullTrace right},
        u ∈ convHullTrace left X →
        v ∈ PrRelaxedSetChain r hr right {traceOutput u} →
        LayerChain.spliceTrace u v ∈ PrRelaxedSetChain r hr whole X) :
    reach f₂ (convexHull Real (reach f₁ X)) ⊆
      PrOutputSet
        (alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s)))
        (pumpNetPr f₁ f₂ s) X := by
  let r := alphaRadius α (layerCount (pumpNetPr f₁ f₂ s))
  let hr : 0 < r := alphaRadius_pos α (layerCount (pumpNetPr f₁ f₂ s))
  have hrs : r ≤ s := by
    simpa [r] using hlarge
  have hglue' :
      ∀ {u :
          FullTrace
            (LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r))}
        {v :
          FullTrace
            (LayerChain.appendChain (LayerChain.idChain d' r)
              (LayerChain.FlattenNet (prependIds (2 * (s - r)) f₂)))},
        u ∈ convHullTrace
            (LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r)) X →
        v ∈ PrRelaxedSetChain r hr
            (LayerChain.appendChain (LayerChain.idChain d' r)
              (LayerChain.FlattenNet (prependIds (2 * (s - r)) f₂)))
            {traceOutput u} →
        LayerChain.spliceTrace u v ∈
          PrRelaxedSetChain r hr
            (LayerChain.appendChain
              (LayerChain.appendChain (LayerChain.FlattenNet f₁) (LayerChain.idChain d' r))
              (LayerChain.appendChain (LayerChain.idChain d' r)
                (LayerChain.FlattenNet (prependIds (2 * (s - r)) f₂))))
            X := by
    intro u v hu hv
    exact hglue hu hv
  exact reach_conv_middle_subset_PrOutputSet_pump_of_glue_buffer
    (r := r) (s := s) hr hrs f₁ f₂ X hglue'

end

end Net
