import Std

namespace HornCycleReadouts

/-- Sum bits with multiplicity over the list of permitted local choices. -/
def parity (xs : List ι) (f : ι → Bool) : Bool :=
  match xs with
  | [] => false
  | a :: rest => (f a).xor (parity rest f)

private theorem exchange (a b c d : Bool) :
    (a.xor b).xor (c.xor d) = (a.xor c).xor (b.xor d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem split (xs : List ι) (f g : ι → Bool) :
    parity xs (fun a => (f a).xor (g a)) = (parity xs f).xor (parity xs g) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simpa only [parity, ih] using exchange (f a) (g a) (parity rest f) (parity rest g)

private theorem cancel_copy (a b c : Bool) :
    (a.xor b).xor (b.xor c) = a.xor c := by
  cases a <;> cases b <;> cases c <;> decide

/-- Off-diagonal pairs of local choices cancel when the two edges are swapped. -/
theorem square_diag (xs : List ι) (B : ι → ι → Bool) (symm : ∀ a b, B a b = B b a) :
    parity xs (fun a => parity xs (B a)) = parity xs (fun a => B a a) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    change ((B a a).xor (parity rest (B a))).xor
      (parity rest (fun b => (B b a).xor (parity rest (B b)))) =
      (B a a).xor (parity rest (fun b => B b b))
    rw [split, ih]
    have col : (fun b => B b a) = B a := funext (fun b => symm b a)
    rw [col]
    exact cancel_copy _ _ _

def loopOK (R : α → α → Prop) := ∃ x, R x x

def cycleOK (R S : α → α → Prop) := ∃ x y, R x y ∧ S y x

theorem swap_edges (R S : α → α → Prop) : cycleOK R S ↔ cycleOK S R := by
  constructor <;> rintro ⟨x, y, h, k⟩ <;> exact ⟨y, x, k, h⟩

/-- Applies to bit-vector interfaces of any arity and to projected Horn relations. -/
theorem diagonal_iff (op : α → α → α) (comm : ∀ x y, op x y = op y x)
    (R : α → α → Prop)
    (closed : ∀ a b c d, R a b → R c d → R (op a c) (op b d)) :
    cycleOK R R ↔ loopOK R := by
  constructor
  · rintro ⟨x, y, h, k⟩
    have m := closed x y y x h k
    rw [← comm x y] at m
    exact ⟨_, m⟩
  · rintro ⟨x, h⟩
    exact ⟨x, x, h, h⟩

/-- The two-vertex test cannot distinguish a transposition from two
    correct self-reads by any such single-decision parity readout. -/
theorem cycle_readout (xs : List ι) (Rs : ι → α → α → Prop)
    (op : α → α → α) (comm : ∀ x y, op x y = op y x)
    (closed : ∀ i a b c d, Rs i a b → Rs i c d → Rs i (op a c) (op b d)) :
    (letI := Classical.propDecidable
     parity xs (fun i => parity xs (fun j => decide (cycleOK (Rs i) (Rs j)))) =
     parity xs (fun i => decide (loopOK (Rs i)))) := by
  classical
  change parity xs (fun i => parity xs ((fun i j => decide (cycleOK (Rs i) (Rs j))) i)) = _
  rw [square_diag xs _ (fun i j => by simp only [swap_edges (Rs i) (Rs j)])]
  exact congrArg (parity xs) (funext (fun i => by
    rw [diagonal_iff op comm (Rs i) (closed i)]))

def diseq (a b : Bool) : Prop := a ≠ b

private theorem diseq_no_loop : ¬ loopOK diseq := by
  rintro ⟨a, ha⟩
  exact ha rfl

theorem cycle_without_loop (R : Bool → Bool → Prop) (noLoop : ¬ loopOK R) :
    cycleOK R R ↔ R = diseq := by
  constructor
  · rintro ⟨x, y, f, g⟩
    have distinct : x ≠ y := by
      rintro rfl
      exact noLoop ⟨x, f⟩
    have both : R false true ∧ R true false := by
      cases x <;> cases y <;> simp_all
    funext a b
    apply propext
    cases a <;> cases b
    · exact ⟨fun h => False.elim (noLoop ⟨_, h⟩), fun h => False.elim (h rfl)⟩
    · exact ⟨fun _ => by simp [diseq], fun _ => both.1⟩
    · exact ⟨fun _ => by simp [diseq], fun _ => both.2⟩
    · exact ⟨fun h => False.elim (noLoop ⟨_, h⟩), fun h => False.elim (h rfl)⟩
  · rintro rfl
    exact ⟨false, true, by simp [diseq], by simp [diseq]⟩

theorem boolean_defect (xs : List ι) (Rs : ι → Bool → Bool → Prop) :
    (letI := Classical.propDecidable
     parity xs (fun i => parity xs (fun j => decide (cycleOK (Rs i) (Rs j)))) =
      (parity xs (fun i => decide (loopOK (Rs i)))).xor
        (parity xs (fun i => decide (Rs i = diseq)))) := by
  classical
  change parity xs (fun i => parity xs ((fun i j => decide (cycleOK (Rs i) (Rs j))) i)) = _
  rw [square_diag xs _ (fun i j => by simp only [swap_edges (Rs i) (Rs j)]), ← split]
  apply congrArg (parity xs)
  funext i
  by_cases h : loopOK (Rs i)
  · have cyc : cycleOK (Rs i) (Rs i) := by obtain ⟨x, hx⟩ := h; exact ⟨x, x, hx, hx⟩
    have ne : Rs i ≠ diseq := fun eq => diseq_no_loop (eq ▸ h)
    simp [cyc, h, ne]
  · simp [cycle_without_loop (Rs i) h, h]

end HornCycleReadouts
