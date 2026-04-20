import MultiNeuron.Relaxation.Layerwise

open Set

namespace Net

/-
This file formalizes Lemma 3.1 in the paper.
-/

/--
Projection of the P₁ relaxed set of `Net.comp f₁ f₂` to the
intermediate split-layer output.
-/
def splitProjection {n m k : Nat} (f₁ : Net n m) (f₂ : Net m k) (X : Polytope n) :
    Set (Coord m) :=
  (fun t : Trace (Net.comp f₁ f₂) => traceOutput f₁ (t.1, t.2.1)) '' P1RelaxedSetOnPolytope (Net.comp f₁ f₂) X

/--
Lemma 3.1 in the paper: projecting the full `P₁` constraint system of a
composed network to the split variable yields exactly the `P₁` feasible set of
the prefix. In other words, suffix constraints do not change the prefix feasible set.
-/
theorem lemma31 {n m k : Nat} (f₁ : Net n m) (f₂ : Net m k) (X : Polytope n) :
    splitProjection f₁ f₂ X = P1OutputSetOnPolytope f₁ X := by
  ext v
  constructor
  ·
    rintro ⟨⟨x, tf, tg⟩, ht, rfl⟩
    ---use ⟨x, tf⟩
    refine ⟨(x, tf), ?_, rfl⟩
    exact ((mem_P1RelaxedSet_comp f₁ f₂ x tf tg X.feasibleSet).mp ht).left
  · rintro ⟨⟨x, tf⟩, ht, rfl⟩
    refine ⟨(x, (tf, exactTraceVarSingleInput f₂ (traceOutput f₁ (x, tf)))), ?_, rfl⟩
    have hv : traceOutput f₁ (x, tf) ∈ P1OutputSet f₁ X.feasibleSet := ⟨(x, tf), ht, rfl⟩
    exact (mem_P1RelaxedSet_comp f₁ f₂ x tf
      (exactTraceVarSingleInput f₂ (traceOutput f₁ (x, tf))) X.feasibleSet).2
      ⟨ht, exactTrace_mem_P1RelaxedSet_of_mem f₂ hv⟩

end Net
