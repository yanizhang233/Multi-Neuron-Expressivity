import MultiNeuron.Network.Core

open Set

namespace MultiNeuron

/-!
unit tests for the definitions and simplifications in `MultiNeuron.Network.Core`.
-/


section CoreTests

def x : Coord 2 := ![3, -2]

def A : Matrix (Fin 2) (Fin 2) Real := !![1, 2; -3, 4]

def b : Coord 2 := ![5, 4]

def affineOut : Coord 2 := ![4, -13] --A x + b

def reluOut : Coord 2 := ![3, 0] -- relu x

def composedOut : Coord 2 := ![4, 0] -- relu (A x + b)

def singletonInput : Set (Coord 2) := {x}

def affineNet : Net 2 2 := Net.affineLayer A b

def reluNet : Net 2 2 := Net.reluLayer 2

def composedNet : Net 2 2 := Net.comp affineNet reluNet


--test the definition of Coord n
example : x 0 = 3 := by rfl

example : x 1 = -2 := by
  norm_num [x]

--test the definition of the relu function. It is continuous.
example : relu x = reluOut := by
  ext i
  fin_cases i <;> simp [relu, x, reluOut]



example : Continuous (relu : Coord 2 → Coord 2) :=
  continuous_relu

--test the definition of affine layer.
example : affinemap A b x = Matrix.mulVec A x + b := by rfl
  --affineLayer_apply A b x

example : affinemap A b x = affineOut := by
  ext i
  fin_cases i
  <;> norm_num [affinemap, A, b, x, affineOut, Matrix.mulVec]

example : Continuous (affinemap A b : Coord 2 → Coord 2) :=
  continuous_affinemap A b

--test the definition of Net
example : Net.eval (Net.idLayer 2) = _root_.id := by rfl
  --Net.eval_id 2

example : Net.eval affineNet = affinemap A b := by rfl
  --simp [affineNet]

example : Net.eval reluNet = relu := by rfl
  --simp [reluNet]

example : Net.eval composedNet = Net.eval reluNet ∘ Net.eval affineNet := by rfl
  --simp [composedNet]

example : Net.eval composedNet x = composedOut := by
  ext i
  fin_cases i <;> norm_num [composedNet, affineNet, reluNet, Net.eval, affinemap, relu,
    A, b, x, composedOut, Matrix.mulVec]

example : Net.reach (Net.idLayer 2) singletonInput = singletonInput := by
  ext y
  simp [Net.reach]

example : affineOut ∈ Net.reach affineNet singletonInput := by
  use x
  simp [singletonInput]
  ext i
  fin_cases i <;> norm_num [affineNet, Net.eval, affinemap, A, b, x, affineOut, Matrix.mulVec]

example : composedOut ∈ Net.reach composedNet singletonInput := by
  use x
  simp [singletonInput]
  ext i
  fin_cases i <;> norm_num [composedNet, affineNet, reluNet, Net.eval, affinemap, relu,
    A, b, x, composedOut, Matrix.mulVec]

example : Net.reach composedNet singletonInput = ({composedOut} : Set (Coord 2)) := by
  ext y
  constructor
  · rintro ⟨x', hx', rfl⟩
    simp [singletonInput] at hx'
    rw[hx']
    have : Net.eval composedNet x = composedOut := by
      ext i
      fin_cases i <;> norm_num [composedNet, affineNet, reluNet, Net.eval, affinemap, relu,
      A, b, x, composedOut, Matrix.mulVec]
    simpa
  · intro hy
    rw[Set.mem_singleton_iff] at hy
    use x
    simp [singletonInput]
    rw[hy]
    ext i
    fin_cases i <;> norm_num [composedNet, affineNet, reluNet, Net.eval, affinemap, relu,
      A, b, x, composedOut, Matrix.mulVec]



end CoreTests

end MultiNeuron
