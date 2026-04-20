import MultiNeuron.Relaxation.Layerwise

open Set

namespace MultiNeuron
namespace Net
namespace LayerwiseTest

/-!
Regression tests for `MultiNeuron.Relaxation.Layerwise`.

Each `example` is a Lean-native unit test for one of the core definitions or
theorems in the layerwise relaxation development.
-/

section LayerwiseTests

def x : Coord 2 := ![3, -2]

def A : Matrix (Fin 2) (Fin 2) Real := !![1, 2; -3, 4]

def b : Coord 2 := ![5, 4]

def affineOut : Coord 2 := ![4, -13]

def reluOut : Coord 2 := ![3, 0]

def composedOut : Coord 2 := ![4, 0]

def singletonInput : Set (Coord 2) := {x}

def affineNet : Net 2 2 := Net.affine A b

def reluNet : Net 2 2 := Net.relu 2

def composedNet : Net 2 2 := Net.comp affineNet reluNet

lemma affineLayer_x : affineLayer A b x = affineOut := by
  ext i
  fin_cases i <;> norm_num [affineLayer, A, b, x, affineOut, Matrix.mulVec]

lemma relu_x : MultiNeuron.relu x = reluOut := by
  ext i
  fin_cases i <;> norm_num [MultiNeuron.relu, x, reluOut]

lemma relu_affineOut : MultiNeuron.relu affineOut = composedOut := by
  ext i
  fin_cases i <;> norm_num [MultiNeuron.relu, affineOut, composedOut]

example : affineLayerMap A b x = affineLayer A b x :=
  affineLayerMap_apply A b x

example : affineLayerMap A b x = affineOut := by
  rw [affineLayerMap_apply, affineLayer_x]

example : relax (Net.id 2) singletonInput = singletonInput :=
  relax_id singletonInput

example : relax affineNet singletonInput = affineLayer A b '' singletonInput := by
  simp [affineNet]

example : relax reluNet singletonInput = convexHull Real (MultiNeuron.relu '' singletonInput) := by
  simp [reluNet]

example : relax composedNet singletonInput = relax reluNet (relax affineNet singletonInput) := by
  simp [composedNet]

example : relax affineNet singletonInput = {affineOut} := by
  simp [affineNet, singletonInput, affineLayer_x]

example : relax reluNet singletonInput = {reluOut} := by
  simp [reluNet, singletonInput, relu_x, convexHull_singleton]

example :
    Prod.snd '' convexHull Real (functionGraph MultiNeuron.relu singletonInput) = {reluOut} := by
  simpa [singletonInput, relu_x, convexHull_singleton] using
    (snd_image_convexHull_functionGraph (f := MultiNeuron.relu) singletonInput)

example : relax composedNet singletonInput = {composedOut} := by
  simp [composedNet, affineNet, reluNet, singletonInput, affineLayer_x, relu_affineOut,
    convexHull_singleton]

example : Monotone (relax composedNet) :=
  relax_mono composedNet

example : relax composedNet singletonInput ⊆ relax composedNet (Set.univ : Set (Coord 2)) :=
  relax_mono composedNet (Set.subset_univ singletonInput)

example : Convex Real (relax composedNet singletonInput) :=
  relax_convex composedNet (by simp [singletonInput])

example : reach composedNet singletonInput ⊆ relax composedNet singletonInput :=
  reach_subset_relax composedNet singletonInput

example : convexHull Real (reach affineNet singletonInput) ⊆ relax affineNet singletonInput :=
  convex_reach_prefix_subset_relax_prefix (f := affineNet) (X := singletonInput) (by
    simp [singletonInput])

example : reach reluNet (relax affineNet singletonInput) ⊆ relax reluNet (relax affineNet singletonInput) :=
  reach_suffix_on_relaxed_input_subset_relax_suffix reluNet (relax affineNet singletonInput)

example :
    reach reluNet (convexHull Real (reach affineNet singletonInput)) ⊆
      relax composedNet singletonInput := by
  simpa [composedNet] using
    reach_comp_prefix_convex_subset_relax_comp
      (f₁ := affineNet) (f₂ := reluNet) (X := singletonInput) (by simp [singletonInput])

example : reach affineNet singletonInput ⊆ relax affineNet singletonInput := by
  simpa [affineNet] using reach_affine_subset_relax_affine A b singletonInput

example : reach reluNet singletonInput ⊆ relax reluNet singletonInput := by
  simpa [reluNet] using reach_relu_subset_relax_relu singletonInput

end LayerwiseTests

end LayerwiseTest
end Net
end MultiNeuron
