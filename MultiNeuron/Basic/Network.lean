--import Mathlib
--import .Topology.Basic

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Algebra.Module.FiniteDimension


open Set



/-
This file formally defines feedforward ReLU neural networks.
-/

/-- `Coord n` is the space of `n`-dimensional real vectors. -/
abbrev Coord (n : Nat) := Fin n → Real

/--
definition of ReLU.
-/
def relu {n : Nat} : Coord n → Coord n := fun x i ↦ max (x i) 0

/--
ReLU is continuous. Need this theorem later to show that the output set produced by P₁ is always bounded.
-/
theorem continuous_relu {n : Nat} : Continuous (relu : Coord n → Coord n) := by
  refine continuous_pi ?_
  intro i
  have : Continuous (fun a ↦ relu a i) := Continuous.max (continuous_apply i) continuous_const
  assumption



/--
affine map `x ↦ A x + b`, `A` is the associated matrix, `b` is the associated bias vector.
-/
def affinemap {n m : Nat} (A : Matrix (Fin m) (Fin n) Real) (b : Coord m) : Coord n → Coord m :=
  fun x ↦ Matrix.mulVec A x + b

noncomputable def affineLayerMap {n m : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (b : Coord m) : Coord n →ᵃ[Real] Coord m :=
  A.mulVecLin.toAffineMap +ᵥ AffineMap.const Real (Coord n) b


-- theorem affinemap_apply {n m : Nat} (A : Matrix (Fin m) (Fin n) Real) (b : Coord m) (x : Coord n) :
--     affinemap A b x = Matrix.mulVec A x + b := rfl

/--
affine map is continuous. Need this theorem later to show that the output set produced by P₁ is always bounded.
-/
theorem continuous_affinemap {n m : Nat} (A : Matrix (Fin m) (Fin n) Real) (b : Coord m) :
    Continuous (affinemap A b : Coord n → Coord m) :=
    Continuous.add (LinearMap.continuous_of_finiteDimensional A.mulVecLin) continuous_const



/--
`Net n m` is a neural network with `n` input nodes and `m` output nodes, defined inductively.
-/
inductive Net : Nat → Nat → Type where
  | idLayer (n : Nat) : Net n n
  | affineLayer {n m : Nat} (A : Matrix (Fin m) (Fin n) Real) (b : Coord m) : Net n m
  | reluLayer (n : Nat) : Net n n
  | comp {n m k : Nat} : Net n m → Net m k → Net n k




namespace Net

/--
Semantic of a ReLU neural network.
eval takes a Net and returns the network function.
-/
def eval {n m : Nat} : Net n m → Coord n → Coord m
  | .idLayer _ => _root_.id
  | .affineLayer A b => affinemap A b
  | .reluLayer _ => relu
  | .comp N₁ N₂ => eval N₂ ∘ eval N₁


theorem continuous_eval : {n m : Nat} → (f : Net n m) → Continuous (eval f)
  | _, _, .idLayer _ => by
      simpa [Net.eval] using (continuous_id : Continuous (fun x : Coord _ => x))
  | _, _, .affineLayer A b => by simpa [Net.eval] using continuous_affinemap A b
  | _, _, .reluLayer _ => by simpa [Net.eval] using (continuous_relu : Continuous (relu : Coord _ → Coord _))
  | _, _, .comp f g => by
      simpa [Net.eval] using (continuous_eval g).comp (continuous_eval f)


/--
Example: single-hidden layer network
`x ↦ A₂ (relu (A₁ x + b₁)) + b₂`
-/
def twoLayerNet {n h m : Nat}
    (A₁ : Matrix (Fin h) (Fin n) Real) (b₁ : Coord h)
    (A₂ : Matrix (Fin m) (Fin h) Real) (b₂ : Coord m) :
    Net n m :=
  Net.comp
    (Net.comp (Net.affineLayer A₁ b₁) (Net.reluLayer h))
    (Net.affineLayer A₂ b₂)


/-add these theorems to [simp] to make proof cleaner-/
@[simp] theorem eval_id (n : Nat) : eval (Net.idLayer n) = _root_.id := rfl
@[simp] theorem eval_relu (n : Nat) : eval (Net.reluLayer n) = relu := rfl
@[simp] theorem eval_comp {n m k : Nat} (N₁ : Net n m) (N₂ : Net m k) :
    eval (Net.comp N₁ N₂) = eval N₂ ∘ eval N₁ := rfl

/--
The exact reachable set of a network on an input set `X`, i.e., the image set `f(x)`.
-/
def reach {n m : Nat} (f : Net n m) (X : Set (Coord n)) : Set (Coord m) := eval f '' X

-- /--
-- Reachability is monotone with respect to the input set.
-- For a neural network `f`, for two subsets `X, Y ⊆ Coord n`, if `X ⊆ Y`, then the reachable set of `f` on `X` is a subset of the reachable set on `Y`.
-- -/
-- theorem reach_mono {n m : Nat} (f : Net n m) : Monotone (reach f) := by
--   rintro X Y hXY y ⟨x, hx, hxy⟩
--   exact ⟨x, hXY hx, hxy⟩

/--
if the input set is nonempty, then the reachable set is nonempty.
-/
theorem reach_nonempty {n m : Nat} (f : Net n m) {X : Set (Coord n)} (hX : X.Nonempty) :
    (reach f X).Nonempty := by
  rcases hX with ⟨x, hx⟩
  use eval f x
  use x


end Net
