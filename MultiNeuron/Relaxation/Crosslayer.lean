import MultiNeuron.Basic.Polytope
import Mathlib.Analysis.Convex.Hull

open Set

namespace Net

noncomputable section

/-!
Draft file: sliding-window cross-layer relaxation `P_r`.

Unlike the built module `MultiNeuron/Relaxation/Crosslayer.lean`, this file
follows the definition in the paper more literally:

* flatten the network into primitive layers,
* keep a full trace `(v⁽⁰⁾, v⁽¹⁾, ..., v⁽ᴸ⁾)`,
* if the remaining suffix has at most `r` layers, relax that whole suffix at once,
* otherwise impose the convex-hull constraint on the first `r` consecutive
  layers and recurse on the suffix starting from layer 2.

So the windows overlap:

`(v⁽⁰⁾,...,v⁽ʳ⁾), (v⁽¹⁾,...,v⁽ʳ⁺¹⁾), (v⁽²⁾,...,v⁽ʳ⁺²⁾), ...`
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

/-- One-step output relaxation: convex hull of the exact output set. -/
def blockRelax {n m : Nat} (f : Net n m) (X : Set (Coord n)) : Set (Coord m) :=
  convexHull Real (reach f X)

/-- Exact outputs are contained in the one-step relaxation. -/
theorem reach_subset_blockRelax {n m : Nat} (f : Net n m) (X : Set (Coord n)) :
    reach f X ⊆ blockRelax f X := by
  exact subset_convexHull Real (reach f X)

namespace LayerChain

/-- A network flattened into a left-to-right list of layers. -/
inductive T : Nat → Nat → Type where
  | nil (n : Nat) : T n n
  | cons {n m k : Nat} (f : Net n m) (hcount : layerCount f ≤ 1) (rest : T m k) : T n k

/-- Number of layers in the chain. -/
def length : {n m : Nat} → T n m → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ _ rest => Nat.succ (length rest)

/-- Append two chains. -/
def append : {n m k : Nat} → T n m → T m k → T n k
  | _, _, _, .nil _, tail => tail
  | _, _, _, .cons f h rest, tail => .cons f h (append rest tail)

/-- Flatten a network into primitive layers. -/
def ofNet : {n m : Nat} → Net n m → T n m
  | _, _, .idLayer n => .cons (Net.idLayer n) (by simp [layerCount]) (.nil n)
  | _, _, .affineLayer A b => .cons (Net.affineLayer A b) (by simp [layerCount]) (.nil _)
  | _, _, .reluLayer n => .cons (Net.reluLayer n) (by simp [layerCount]) (.nil n)
  | _, _, .comp f g => append (ofNet f) (ofNet g)

/-- Recompose a flattened chain into a network. -/
def toNet : {n m : Nat} → T n m → Net n m
  | n, _, .nil _ => Net.idLayer n
  | _, _, .cons f _ rest => Net.comp f (toNet rest)

/-- Take the first `k` layers of a chain. -/
def take : {n m : Nat} → Nat → T n m → Σ mid, T n mid
  | n, _, 0, _ => ⟨n, .nil n⟩
  | n, _, _ + 1, .nil _ => ⟨n, .nil n⟩
  | _, _, k + 1, .cons f h rest =>
      let p := take k rest
      ⟨p.1, .cons f h p.2⟩

@[simp] theorem length_append {n m k : Nat} (c₁ : T n m) (c₂ : T m k) :
    length (append c₁ c₂) = length c₁ + length c₂ := by
  induction c₁ with
  | nil n =>
      simp [append, length]
  | cons f h rest ih =>
      simp [append, length, ih, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm]

@[simp] theorem length_ofNet {n m : Nat} (f : Net n m) :
    length (ofNet f) = layerCount f := by
  induction f with
  | idLayer n =>
      simp [ofNet, length, layerCount]
  | affineLayer A b =>
      simp [ofNet, length, layerCount]
  | reluLayer n =>
      simp [ofNet, length, layerCount]
  | comp f g ihf ihg =>
      simp [ofNet, layerCount, length_append, ihf, ihg]

/--appending two chains is functionally equivalent to composing the network funtions -/
@[simp] theorem eval_toNet_append {n m k : Nat} (c₁ : T n m) (c₂ : T m k) :
    eval (toNet (append c₁ c₂)) = eval (toNet c₂) ∘ eval (toNet c₁) := by
  induction c₁ with
  | nil n =>
      funext x
      simp [append, toNet]
  | cons f h rest ih =>
      funext x
      simp [append, toNet, ih]

/--flatten a network to a chain, and then revert the chain back to the network, does not change the network function. -/
@[simp] theorem eval_toNet_ofNet {n m : Nat} (f : Net n m) :
    eval (toNet (ofNet f)) = eval f := by
  induction f with
  | idLayer n =>
      funext x
      simp [ofNet, toNet, Net.eval]
  | affineLayer A b =>
      funext x
      simp [ofNet, toNet, Net.eval]
  | reluLayer n =>
      funext x
      simp [ofNet, toNet, Net.eval]
  | comp f g ihf ihg =>
      funext x
      simp [ofNet, Net.eval, ihf, ihg]

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

/-- reading off input variable `v⁽⁰⁾` of a full trace. -/
def traceInput : {n m : Nat} → {c : LayerChain.T n m} → FullTrace c → Coord n
  | _, _, .nil _, x => x
  | _, _, .cons _ _ _, t => t.1

/-- reading off final output variable of a full trace. -/
def traceOutput : {n m : Nat} → {c : LayerChain.T n m} → FullTrace c → Coord m
  | _, _, .nil _, x => x
  | _, _, .cons _ _ _, t => traceOutput t.2

/-- Suffix trace starting at layer 2. -/
def tailTrace {n m k : Nat} {f : Net n m} {hcount : layerCount f ≤ 1}
    {rest : LayerChain.T m k} :
    FullTrace (.cons f hcount rest) → FullTrace rest
  | t => t.2

/-- The exact full trace evaluated at a single input. -/
def exactTraceSingleInput :
    {n m : Nat} → (c : LayerChain.T n m) → Coord n → FullTrace c
  | _, _, .nil _, x => x
  | _, _, .cons f _ rest, x =>
      show Coord _ × FullTrace rest from (x, exactTraceSingleInput rest (eval f x))

/-- The exact full trace evaluated at an input set. -/
def exactTraceSet {n m : Nat} (c : LayerChain.T n m) (X : Set (Coord n)) : Set (FullTrace c) :=
  exactTraceSingleInput c '' X

/--
the convex hull of the exact full trace set on the input set.
-/
def windowRelaxedSet {n m : Nat} (c : LayerChain.T n m) (X : Set (Coord n)) : Set (FullTrace c) :=
  convexHull Real (exactTraceSet c X)

/-- First `k` variables of a full trace. -/
def traceTake : {n m : Nat} → (k : Nat) → (c : LayerChain.T n m) →
    FullTrace c → FullTrace (LayerChain.take k c).2
  | _, _, 0, _, t => traceInput t
  | _, _, _ + 1, .nil _, t => traceInput t
  | _, _, k + 1, .cons _ _ rest, t =>
      show Coord _ × FullTrace (LayerChain.take k rest).2 from (t.1, traceTake k rest t.2)

@[simp] theorem traceInput_exactTraceSingleInput {n m : Nat}
    (c : LayerChain.T n m) (x : Coord n) :
    traceInput (exactTraceSingleInput c x) = x := by
  induction c with
  | nil n =>
      rfl
  | cons f h rest ih =>
      rfl

@[simp] theorem traceOutput_exactTraceSingleInput {n m : Nat}
    (c : LayerChain.T n m) (x : Coord n) :
    traceOutput (exactTraceSingleInput c x) = eval (LayerChain.toNet c) x := by
  induction c with
  | nil n =>
      rfl
  | cons f h rest ih =>
      simpa [exactTraceSingleInput, traceOutput, LayerChain.toNet, Net.eval] using
        ih (eval f x)

@[simp] theorem traceTake_exactTraceSingleInput :
    {n m : Nat} → (k : Nat) → (c : LayerChain.T n m) → (x : Coord n) →
      traceTake k c (exactTraceSingleInput c x) =
        exactTraceSingleInput (LayerChain.take k c).2 x
  | n, _, 0, c, x => by
      cases c <;> rfl
  | n, _, _ + 1, .nil _, x => by
      rfl
  | _, _, k + 1, .cons f h rest, x => by
      simp [traceTake, LayerChain.take, exactTraceSingleInput, traceTake_exactTraceSingleInput]

/-- Exact traces are contained in the window relaxation. -/
theorem exactTrace_mem_windowRelaxedSet_of_mem {n m : Nat}
    (c : LayerChain.T n m) {X : Set (Coord n)} {x : Coord n} (hx : x ∈ X) :
    exactTraceSingleInput c x ∈ windowRelaxedSet c X := by
  exact subset_convexHull Real (exactTraceSet c X) ⟨x, hx, rfl⟩

/--
sliding-window cross-layer relaxation on a flattened chain.
If the remaining suffix has at most `r` layers, relax it in one shot.
Otherwise:
1. process the first `r` consecutive layers by their exact convex hull;
2. recurse on the suffix starting from layer 2, with input set equal to the
   projection of the first local window to `v⁽¹⁾`, i.e. `blockRelax` of the
   first primitive layer.
-/
def PrRelaxedSetChain (r : Nat) (hr : 0 < r) :
    {n m : Nat} → (c : LayerChain.T n m) → Set (Coord n) → Set (FullTrace c)
  | _, _, .nil n, X => windowRelaxedSet (.nil n) X
  | _, _, .cons f hcount rest, X =>
      let c : LayerChain.T _ _ := .cons f hcount rest
      if _hlen : LayerChain.length c ≤ r then
        windowRelaxedSet c X
      else
        let pref := (LayerChain.take r c).2
        {t | traceTake r c t ∈ windowRelaxedSet pref X ∧
            tailTrace t ∈ PrRelaxedSetChain r hr rest (blockRelax f X)}
termination_by n m c _ => LayerChain.length c
decreasing_by
  simp [LayerChain.length]

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
        exactTrace_mem_windowRelaxedSet_of_mem (.nil n) hx
  | _, _, .cons f hcount rest, X, x, hx => by
      let c : LayerChain.T _ _ := .cons f hcount rest
      by_cases hlen : LayerChain.length c ≤ r
      · simpa [PrRelaxedSetChain, c, hlen] using
          exactTrace_mem_windowRelaxedSet_of_mem c hx
      · simp [PrRelaxedSetChain, c, hlen]
        refine ⟨?_, ?_⟩
        · simpa [c, traceTake_exactTraceSingleInput] using
            exactTrace_mem_windowRelaxedSet_of_mem ((LayerChain.take r c).2) hx
        · have hy : eval f x ∈ blockRelax f X := by
            exact reach_subset_blockRelax f X ⟨x, hx, rfl⟩
          simpa [tailTrace, exactTraceSingleInput] using
            exactTrace_mem_PrRelaxedSetChain_of_mem r hr rest hy


theorem reach_toNet_subset_PrOutputSetChain
    (r : Nat) (hr : 0 < r) {n m : Nat} (c : LayerChain.T n m) (X : Set (Coord n)) :
    reach (LayerChain.toNet c) X ⊆ PrOutputSetChain hr c X := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨exactTraceSingleInput c x, exactTrace_mem_PrRelaxedSetChain_of_mem r hr c hx, ?_⟩
  exact traceOutput_exactTraceSingleInput c x

/-- definition of P_r: sliding-window relaxed trace set for a network. -/
def PrRelaxedSet {r n m : Nat}
    (hr : 0 < r) (f : Net n m) (X : Set (Coord n)) :
    Set (FullTrace (LayerChain.ofNet f)) :=
  PrRelaxedSetChain r hr (LayerChain.ofNet f) X

/--feasible output set for a network induced by Pr. -/
def PrOutputSet {r n m : Nat}
    (hr : 0 < r) (f : Net n m) (X : Set (Coord n)) : Set (Coord m) :=
  PrOutputSetChain hr (LayerChain.ofNet f) X

/-- P_r on a polytope input. -/
def PrOutputSetOnPolytope {r n m : Nat}
    (hr : 0 < r) (f : Net n m) (X : Polytope n) : Set (Coord m) :=
  PrOutputSet hr f X.feasibleSet

/-- Pr is sound: feasible output set for a network induced by Pr is a superset of the exact reachable set. -/
theorem reach_subset_PrOutputSet {r n m : Nat}
    (hr : 0 < r) (f : Net n m) (X : Set (Coord n)) :
    reach f X ⊆ PrOutputSet hr f X := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨exactTraceSingleInput (LayerChain.ofNet f) x,
    exactTrace_mem_PrRelaxedSetChain_of_mem r hr (LayerChain.ofNet f) hx, ?_⟩
  rw [traceOutput_exactTraceSingleInput, LayerChain.eval_toNet_ofNet]

end

end Net
