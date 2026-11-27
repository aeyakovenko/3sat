import Std

namespace DiagonalQueryReplay

abbrev Point (ι : Type) := ι → Bool
abbrev Matrix (ι : Type) := ι → ι → Bool

def parity (coordinates : List ι) (f : Point ι) : Bool :=
  match coordinates with
  | [] => false
  | i :: rest => f i ^^ parity rest f

def dot (coordinates : List ι) (z x : Point ι) : Bool :=
  parity coordinates (fun j => z j && x j)

def matvec (coordinates : List ι) (b : Matrix ι) (x : Point ι) : Point ι :=
  fun i => dot coordinates (b i) x

private theorem reorder (a b c d : Bool) : ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  decide +revert

private theorem parityXor (js : List ι) (f g : Point ι) :
    parity js (fun j => f j ^^ g j) = (parity js f ^^ parity js g) := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [parity, ih]; exact reorder ..

private theorem parityScalar (js : List ι) (c : Bool) (f : Point ι) :
    parity js (fun j => c && f j) = (c && parity js f) := by
  induction js with
  | nil => simp [parity]
  | cons j js ih => cases c <;> simp_all [parity]

private theorem distribute (a b c d : Bool) :
    (a && ((b && c) ^^ d)) = ((c && (b && a)) ^^ (a && d)) := by decide +revert

/-- Cross terms cancel in pairs over F₂ for every finite symmetric matrix. -/
theorem quadraticDiagonal (js : List ι) (b : Matrix ι) (x : Point ι)
    (sym : ∀ i j, b i j = b j i) :
    dot js x (matvec js b x) = dot js (fun i => b i i) x := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    have terms : (fun j => x j && ((b j i && x i) ^^ matvec js b x j)) =
        (fun j => (x i && (b i j && x j)) ^^ (x j && matvec js b x j)) := by
      funext j
      rw [sym j i]
      exact distribute ..
    have tail : dot js x (matvec (i :: js) b x) =
        ((x i && matvec js b x i) ^^ dot js x (matvec js b x)) := by
      change parity js (fun j => x j && ((b j i && x i) ^^ matvec js b x j)) = _
      rw [terms, parityXor, parityScalar]
      rfl
    change ((x i && ((b i i && x i) ^^ matvec js b x i)) ^^ dot js x (matvec (i :: js) b x)) =
      ((b i i && x i) ^^ dot js (fun j => b j j) x)
    rw [tail, ih]
    cases x i <;> cases b i i <;> cases matvec js b x i <;> simp

def perturb (b : Matrix ι) (z : Point ι) : Matrix ι :=
  fun i j => b i j ^^ (z i && z j)

theorem diagonalShift (b : Matrix ι) (z : Point ι) (i : ι) :
    perturb b z i i = (b i i ^^ z i) := by simp [perturb]

theorem preservesSymmetry (b : Matrix ι) (z : Point ι) (sym : ∀ i j, b i j = b j i) :
    ∀ i j, perturb b z i j = perturb b z j i := by
  intro i j
  rw [perturb, perturb, sym i j, Bool.and_comm (z i) (z j)]

private theorem stepRule (b v w x d e : Bool) :
    (((b ^^ (v && w)) && x) ^^ (d ^^ (v && e))) =
      (((b && x) ^^ d) ^^ (v && ((w && x) ^^ e))) := by decide +revert

theorem action (coordinates : List ι) (b : Matrix ι) (z x : Point ι) (i : ι) :
    matvec coordinates (perturb b z) x i =
      (matvec coordinates b x i ^^ (z i && dot coordinates z x)) := by
  induction coordinates with
  | nil => simp [matvec, dot, parity]
  | cons j js ih =>
    change (((b i j ^^ (z i && z j)) && x j) ^^ matvec js (perturb b z) x i) = _
    rw [ih]
    exact stepRule (b i j) (z i) (z j) (x j) (matvec js b x i) (dot js z x)

theorem invisible (coordinates : List ι) (b : Matrix ι) (z x : Point ι)
    (orthogonal : dot coordinates z x = false) :
    matvec coordinates (perturb b z) x = matvec coordinates b x := by
  funext i
  simp [action, orthogonal]

inductive Strategy (ι : Type) where
  | stop
  | ask (query : Point ι) (next : Point ι → Strategy ι)

def transcript (oracle : Point ι → Point ι) :
    Strategy ι → List (Point ι × Point ι)
  | .stop => []
  | .ask x next => (x, oracle x) :: transcript oracle (next (oracle x))

/-- Orthogonality is required only on the original adaptive execution. It
    suffices for exact equality of all queries and all answers after the shift. -/
theorem replay (coordinates : List ι) (b : Matrix ι) (z : Point ι) (s : Strategy ι)
    (orthogonal : ∀ t ∈ transcript (matvec coordinates b) s, dot coordinates z t.1 = false) :
    transcript (matvec coordinates (perturb b z)) s = transcript (matvec coordinates b) s := by
  induction s with
  | stop => rfl
  | ask x next ih =>
    have h := orthogonal (x, matvec coordinates b x) (by simp [transcript])
    have same := invisible coordinates b z x h
    simp only [transcript, same, List.cons.injEq, true_and]
    apply ih
    intro t ht
    exact orthogonal t (by simp [transcript, ht])

end DiagonalQueryReplay
