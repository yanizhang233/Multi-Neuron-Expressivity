import MultiNeuron.Relaxation.Crosslayer
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded

open Set

namespace Net

noncomputable section

/-!
Compatibility backend for the older block-decomposition cross-layer proofs.

The main `Crosslayer.lean` file now contains the paper-style sliding-window
definition of `P_r`. Some section 4 polytope proofs in this repo still use an
explicit non-overlapping block decomposition backend, so this file restores the
small API they depend on.
-/

/-- `blockRelax` is by definition the convex hull of the exact reachable set. -/
@[simp] theorem blockRelax_eq_convexHull_reach {n m : Nat} (f : Net n m) (X : Set (Coord n)) :
    blockRelax f X = convexHull Real (reach f X) := rfl

/-- Every network has at least one counted layer. -/
theorem one_le_layerCount : {n m : Nat} → (f : Net n m) → 1 ≤ layerCount f
  | _, _, .idLayer _ => by simp [layerCount]
  | _, _, .affineLayer _ _ => by simp [layerCount]
  | _, _, .reluLayer _ => by simp [layerCount]
  | _, _, .comp f g => by
      exact le_trans (one_le_layerCount f) (Nat.le_add_right _ _)

/-- The network semantics is continuous. -/
theorem continuous_eval {n m : Nat} (f : Net n m) : Continuous (eval f : Coord n → Coord m) := by
  induction f with
  | idLayer _ =>
      simpa [Net.eval] using (continuous_id : Continuous (_root_.id : Coord _ → Coord _))
  | affineLayer A b =>
      simpa [Net.eval] using continuous_affinemap A b
  | reluLayer _ =>
      simpa [Net.eval] using (continuous_relu : Continuous (relu : Coord _ → Coord _))
  | comp f g ihf ihg =>
      simpa [Net.eval] using ihg.comp ihf

/-- A non-overlapping decomposition of a network into consecutive blocks of size at most `r`. -/
inductive BlockDecomposition (r : Nat) : Nat → Nat → Type where
  | single {n m : Nat} (f : Net n m) (hcount : layerCount f ≤ r) : BlockDecomposition r n m
  | comp {n m k : Nat} (f : Net n m) (hcount : layerCount f ≤ r)
      (rest : BlockDecomposition r m k) : BlockDecomposition r n k

namespace BlockDecomposition

/-- Recompose a block decomposition into its network. -/
def toNet {r n m : Nat} : BlockDecomposition r n m → Net n m
  | .single f _ => f
  | .comp f _ rest => Net.comp f (toNet rest)

end BlockDecomposition

/-- The relaxed output set induced by an explicit block decomposition. -/
def PrOutputSetOfDecomposition {r n m : Nat} :
    BlockDecomposition r n m → Set (Coord n) → Set (Coord m)
  | .single f _, X => blockRelax f X
  | .comp f _ rest, X => PrOutputSetOfDecomposition rest (blockRelax f X)

@[simp] theorem PrOutputSetOfDecomposition_single {r n m : Nat}
    (f : Net n m) (hcount : layerCount f ≤ r) (X : Set (Coord n)) :
    PrOutputSetOfDecomposition (.single f hcount) X = blockRelax f X := rfl

@[simp] theorem PrOutputSetOfDecomposition_comp {r n m k : Nat}
    (f : Net n m) (hcount : layerCount f ≤ r) (rest : BlockDecomposition r m k)
    (X : Set (Coord n)) :
    PrOutputSetOfDecomposition (.comp f hcount rest) X =
      PrOutputSetOfDecomposition rest (blockRelax f X) := rfl

/-- `blockRelax` is convex. -/
theorem blockRelax_convex {n m : Nat} (f : Net n m) (X : Set (Coord n)) :
    Convex Real (blockRelax f X) := by
  rw [blockRelax_eq_convexHull_reach]
  exact convex_convexHull Real _

private theorem isBounded_image_of_continuous {n m : Nat} {S : Set (Coord n)}
    {f : Coord n → Coord m} (hf : Continuous f) (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (f '' S) := by
  letI : ProperSpace (Coord n) := FiniteDimensional.proper ℝ (Coord n)
  exact ((hS.isCompact_closure.image hf).isBounded).subset (image_mono subset_closure)

/-- Exact reachable sets of bounded inputs are bounded. -/
theorem reach_bounded {n m : Nat} (f : Net n m) {X : Set (Coord n)}
    (hXbdd : Bornology.IsBounded X) :
    Bornology.IsBounded (reach f X) := by
  simpa [Net.reach] using isBounded_image_of_continuous (continuous_eval f) hXbdd

/-- `blockRelax` preserves boundedness. -/
theorem blockRelax_bounded {n m : Nat} (f : Net n m) {X : Set (Coord n)}
    (hXbdd : Bornology.IsBounded X) :
    Bornology.IsBounded (blockRelax f X) := by
  rw [blockRelax_eq_convexHull_reach]
  exact (isBounded_convexHull).2 (reach_bounded f hXbdd)

/-- The relaxed output set induced by a decomposition is bounded on bounded inputs. -/
theorem PrOutputSetOfDecomposition_bounded {r n m : Nat}
    (D : BlockDecomposition r n m) {X : Set (Coord n)}
    (hXbdd : Bornology.IsBounded X) :
    Bornology.IsBounded (PrOutputSetOfDecomposition D X) := by
  induction D with
  | single f hcount =>
      simpa using blockRelax_bounded f hXbdd
  | comp f hcount rest ih =>
      exact ih (blockRelax_bounded f hXbdd)

end

end Net
