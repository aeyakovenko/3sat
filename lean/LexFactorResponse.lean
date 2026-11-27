import Std

namespace LexFactorResponse

/-- No computational assumptions are needed for soundness. A bounded proposed
    factor procedure is one possible instance of the common response D. -/
theorem earlier_has_response {Matrix Factors : Type} (earlier : Matrix → Matrix → Prop)
    (close : Matrix → Factors → Prop) (a : Matrix) (D : Matrix → Factors)
    (rigid : ∀ w, ¬close a w)
    (respond : ∀ b, earlier b a → close b (D b)) :
    (∀ w, ¬close a w) ∧ ∀ b, earlier b a → ¬(∀ w, ¬close b w) := by
  refine ⟨rigid, ?_⟩
  intro b hb rb
  exact rb (D b) (respond b hb)

/-- An unrestricted response function exists for the actual first rigid matrix
    whenever factors have a default value. Its evaluation cost is a separate premise. -/
theorem unrestricted_response {Matrix Factors : Type} [Inhabited Factors]
    (earlier : Matrix → Matrix → Prop) (close : Matrix → Factors → Prop) (a : Matrix)
    (fails : ∀ b, earlier b a → ∃ w, close b w) :
    ∃ D : Matrix → Factors, ∀ b, earlier b a → close b (D b) := by
  classical
  let D := fun b => if h : ∃ w, close b w then Classical.choose h else default
  refine ⟨D, ?_⟩
  intro b hb
  have witness := fails b hb
  simpa [D, witness] using Classical.choose_spec witness

def Word : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Word n

def addWord : (n : Nat) → Word n → Word n → Word n
  | 0, _, _ => ()
  | n+1, (a, x), (b, y) => (xor a b, addWord n x y)

def total : (n : Nat) → (Word n → Nat) → Nat
  | 0, f => f ()
  | n+1, f => total n (fun x => f (false, x)) + total n (fun x => f (true, x))

private theorem addTotal (n : Nat) (f g : Word n → Nat) :
    total n (fun x => f x + g x) = total n f + total n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp [total, ih]; omega

private theorem scaleTotal (n : Nat) (c : Nat) (f : Word n → Nat) :
    total n (fun x => c * f x) = c * total n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp [total, ih, Nat.mul_add]

private theorem swapTotal (n m : Nat) (f : Word n → Word m → Nat) :
    total n (fun x => total m (f x)) = total m (fun y => total n (fun x => f x y)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [total, ih, addTotal]

private theorem shiftTotal (n : Nat) (x : Word n) (f : Word n → Nat) :
    total n (fun v => f (addWord n x v)) = total n f := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    obtain ⟨a, x⟩ := x
    have lo := ih x (fun y => f (false, y))
    have hi := ih x (fun y => f (true, y))
    cases a <;> simp [total, addWord, lo, hi, Nat.add_comm]

/-- Correlation summed over all binary translations. Boolean membership is the
    special case with f,g taking the values 0 and 1. -/
theorem sum_over_translations (n : Nat) (f g : Word n → Nat) :
    total n (fun v => total n (fun x => f x * g (addWord n x v))) =
      total n f * total n g := by
  rw [swapTotal]
  simp only [scaleTotal, shiftTotal]
  simpa [Nat.mul_comm] using scaleTotal n (total n g) f

private theorem at_most_average (n : Nat) (f : Word n → Nat) :
    ∃ x, 2^n * f x ≤ total n f := by
  induction n with
  | zero => exact ⟨(), by simp [total]⟩
  | succ n ih =>
    obtain ⟨lo, hlo⟩ := ih fun x => f (false, x)
    obtain ⟨hi, hhi⟩ := ih fun x => f (true, x)
    by_cases h : f (false, lo) ≤ f (true, hi)
    · refine ⟨(false, lo), ?_⟩
      have hh := Nat.le_trans (Nat.mul_le_mul_left (2^n) h) hhi
      simpa [total, Nat.pow_succ, Nat.mul_two, Nat.add_mul] using
        Nat.add_le_add hlo hh
    · refine ⟨(true, hi), ?_⟩
      have hl := Nat.le_trans (Nat.mul_le_mul_left (2^n) (Nat.le_of_not_ge h)) hlo
      simpa [total, Nat.pow_succ, Nat.mul_two, Nat.add_mul] using
        Nat.add_le_add hl hhi

/-- If H indicates the uncovered words, adding v to the code leaves uncovered
    exactly the points in H whose translate is also in H. One translation
    achieves the squared-density bound, expressed with integer counts. -/
theorem uncovered_square (n : Nat) (H : Word n → Bool) :
    let h := fun x => (H x).toNat
    ∃ v, 2^n * total n (fun x => h x * h (addWord n x v)) ≤ (total n h)^2 := by
  let h := fun x => (H x).toNat
  obtain ⟨v, hv⟩ := at_most_average n (fun v => total n (fun x => h x * h (addWord n x v)))
  refine ⟨v, ?_⟩
  simpa only [sum_over_translations, Nat.pow_two] using hv

end LexFactorResponse
