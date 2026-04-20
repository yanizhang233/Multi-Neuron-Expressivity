import MultiNeuron.Basic.Network

open Set

/-
This file formally defines a convex polytope:
a bounded set specified by a finite set of linear inequalities.
-/
/--
An affine inequality on `Coord n`, `a · x ≤ b`.
-/
structure AffineInequality (n : Nat) where
  coeff : Coord n
  constant : Real

namespace AffineInequality

/-- The left-hand side `a · x` of an affine inequality `a · x ≤ b`. -/
def lhs {n : Nat} (ineq : AffineInequality n) (x : Coord n) : Real :=
  Finset.univ.sum fun i => ineq.coeff i * x i

/-- Satisfaction of the inequality `a · x ≤ b`. -/
def holds {n : Nat} (ineq : AffineInequality n) (x : Coord n) : Prop :=
  lhs ineq x ≤ ineq.constant

/-- The halfspace cut out by an affine inequality. -/
def halfspace {n : Nat} (ineq : AffineInequality n) : Set (Coord n) :=
  {x | holds ineq x}


@[simp] theorem holds_iff {n : Nat} (ineq : AffineInequality n) (x : Coord n) :
    holds ineq x ↔ Finset.univ.sum (fun i => ineq.coeff i * x i) ≤ ineq.constant := by rfl

@[simp] theorem mem_halfspace {n : Nat} (ineq : AffineInequality n) (x : Coord n) :
    x ∈ halfspace ineq ↔ holds ineq x := by rfl



/-- get the linear map `a · x` from an affine inequality `a · x ≤ b`. -/
def linearMap {n : Nat} (ineq : AffineInequality n) : Coord n →ₗ[Real] Real where
  toFun := lhs ineq
  map_add' := by
    intro x y
    simp [lhs, Finset.sum_add_distrib, mul_add]
  map_smul' := by
    intro c x
    simp [lhs, Finset.mul_sum, mul_assoc, mul_comm]

/-the halfspace of an affine inequality is convex-/
theorem convex_halfspace {n : Nat} (ineq : AffineInequality n) :
    Convex Real (halfspace ineq) := by
  let f : Coord n → Real := lhs ineq
  have hf : IsLinearMap Real f := by
    refine ⟨?_, ?_⟩
    · intro x y
      simp [f, lhs, Finset.sum_add_distrib, mul_add]
    · intro c x
      simp [f, lhs, Finset.mul_sum, mul_assoc, mul_comm]
  simpa [halfspace, holds, linearMap] using
    convex_halfSpace_le hf ineq.constant

end AffineInequality

/--
An H-polyhedron in `Coord n`: a finite intersection of affine halfspaces.
-/
structure HPolyhedron (n : Nat) where
  constraints : Finset (AffineInequality n)

namespace HPolyhedron

/-- The feasible set of an H-polyhedron. -/
def feasibleSet {n : Nat} (P : HPolyhedron n) : Set (Coord n) :=
  {x | ∀ ineq ∈ P.constraints, ineq.holds x}

@[simp] theorem mem_feasibleSet {n : Nat} (P : HPolyhedron n) (x : Coord n) :
    x ∈ P.feasibleSet ↔ ∀ ineq ∈ P.constraints, ineq.holds x := by rfl

/-- The feasible set is exactly the intersection of the individual halfspaces. -/
theorem feasibleSet_eq_iInter {n : Nat} (P : HPolyhedron n) :
    P.feasibleSet = ⋂ ineq ∈ P.constraints, ineq.halfspace := by
  ext x
  simp

-- @[simp] theorem feasibleSet_empty_constraints {n : Nat} :
--     feasibleSet ({ constraints := ∅ } : HPolyhedron n) = Set.univ := by
--   ext x
--   simp

theorem convex_setOf_constraints {n : Nat} (s : Finset (AffineInequality n)) :
    Convex Real {x : Coord n | ∀ ineq ∈ s, ineq.holds x} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (convex_univ : Convex Real (Set.univ : Set (Coord n)))
  | @insert ineq s hs ih =>
      have hhalf : Convex Real ineq.halfspace := ineq.convex_halfspace
      have hrest : Convex Real {x : Coord n | ∀ ineq' ∈ s, ineq'.holds x} := ih
      simpa [AffineInequality.halfspace, Finset.forall_mem_insert, Set.setOf_and] using
        hhalf.inter hrest

/-a Polyhedron is convex-/
theorem convex_feasibleSet {n : Nat} (P : HPolyhedron n) :
    Convex Real P.feasibleSet := by
  simpa [feasibleSet] using convex_setOf_constraints P.constraints

end HPolyhedron

/--
A polytope is a bounded H-polyhedron.
-/
structure Polytope (n : Nat) where
  toHPolyhedron : HPolyhedron n
  bounded_feasibleSet : Bornology.IsBounded toHPolyhedron.feasibleSet

namespace Polytope

/-- The set of points satisfying all inequalities of the polytope. -/
def feasibleSet {n : Nat} (P : Polytope n) : Set (Coord n) :=
  P.toHPolyhedron.feasibleSet

@[simp] theorem mem_feasibleSet {n : Nat} (P : Polytope n) (x : Coord n) :
    x ∈ P.feasibleSet ↔ ∀ ineq ∈ P.toHPolyhedron.constraints, ineq.holds x := by rfl

theorem isBounded_feasibleSet {n : Nat} (P : Polytope n) :
    Bornology.IsBounded P.feasibleSet :=
  P.bounded_feasibleSet

-- theorem feasibleSet_eq_iInter {n : Nat} (P : Polytope n) :
--     P.feasibleSet = ⋂ ineq ∈ P.toHPolyhedron.constraints, AffineInequality.halfspace ineq :=
--   P.toHPolyhedron.feasibleSet_eq_iInter

/- a polytope is convex-/
theorem convex_feasibleSet {n : Nat} (P : Polytope n) :
    Convex Real P.feasibleSet :=
  P.toHPolyhedron.convex_feasibleSet

end Polytope
