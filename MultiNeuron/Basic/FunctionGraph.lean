import MultiNeuron.Basic.Network



/-
Define the function graph, i.e., f[X] in the paper
Prove:
1. the projection of the function graph onto the output coordinate is exactly the image.
2. the projection of the convex hull of the function graph onto the output coordinate is exactly the convex hull of the image.
-/

/--
The graph of a function `f` over an input set `X`, which is the set `{(x, f x): x ∈ X} `.
-/
def functionGraph {n m : Nat} (f : Coord n → Coord m) (X : Set (Coord n)) :
    Set (Coord n × Coord m) :=
  (fun x => (x, f x)) '' X

@[simp] theorem mem_functionGraph {n m : Nat}
    (f : Coord n → Coord m) (X : Set (Coord n)) (x : Coord n) (y : Coord m) :
    (x, y) ∈ functionGraph f X ↔ x ∈ X ∧ y = f x := by
  constructor
  · rintro ⟨x₀, hx₀, hxy⟩
    cases hxy
    exact ⟨hx₀, rfl⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨x, hx, rfl⟩




/--
Projecting the graph of `f` onto the input coordinate recovers the domain `X`.
-/
@[simp] theorem fst_image_functionGraph {n m : Nat}
    (f : Coord n → Coord m) (X : Set (Coord n)) :
    Prod.fst '' functionGraph f X = X := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_functionGraph f X p.1 p.2).mp hp |>.1
  · intro hx
    exact ⟨(x, f x), (mem_functionGraph f X x (f x)).2 ⟨hx, rfl⟩, rfl⟩

 /--
Projecting the graph of `f` onto the output coordinate recovers the image `f(X)`.
-/
@[simp] theorem snd_image_functionGraph {n m : Nat}
    (f : Coord n → Coord m) (X : Set (Coord n)) :
    Prod.snd '' functionGraph f X = f '' X := by
  ext y
  constructor
  -- · rintro ⟨z, ⟨x, hx, h2⟩, hz⟩
  --   use x, hx
  --   rw[← h2] at hz
  --   simp at hz
  --   exact hz
  · rintro ⟨p, hp, rfl⟩
    rcases (mem_functionGraph f X p.1 p.2).mp hp with ⟨hp₁, hp₂⟩
    exact ⟨p.1, hp₁, hp₂.symm⟩
  · rintro ⟨x, hx, rfl⟩
    use (x, f x)
    constructor
    exact (mem_functionGraph f X x (f x)).mpr ⟨hx, rfl⟩
    simp

/--
Projecting the convex hull of the graph of `f` onto the input coordinate gives exactly the convex hull of the input set.
-/
theorem fst_image_convexHull_functionGraph {n m : Nat}
    (f : Coord n → Coord m) (X : Set (Coord n)) :
    Prod.fst '' convexHull Real (functionGraph f X) = convexHull Real X := by
  calc
    Prod.fst '' convexHull Real (functionGraph f X)
      = (LinearMap.fst Real (Coord n) (Coord m)) '' convexHull Real (functionGraph f X) := rfl
    _ = convexHull Real ((LinearMap.fst Real (Coord n) (Coord m)) '' functionGraph f X) :=
      (LinearMap.fst Real (Coord n) (Coord m)).image_convexHull (functionGraph f X)
    _ = convexHull Real X := by simp



/--
Projecting the convex hull of the graph of `f` onto the output coordinate gives exactly the convex hull of `f(X)`.
-/
theorem snd_image_convexHull_functionGraph {n m : Nat}
    (f : Coord n → Coord m) (X : Set (Coord n)) :
    Prod.snd '' convexHull Real (functionGraph f X) = convexHull Real (f '' X) := by
  calc
    Prod.snd '' convexHull Real (functionGraph f X)
      = (LinearMap.snd Real (Coord n) (Coord m)) '' convexHull Real (functionGraph f X) := rfl
    _ = convexHull Real ((LinearMap.snd Real (Coord n) (Coord m)) '' functionGraph f X) := (LinearMap.snd Real (Coord n) (Coord m)).image_convexHull (functionGraph f X)
    _ = convexHull Real (f '' X) := by simp
