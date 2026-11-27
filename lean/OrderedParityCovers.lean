import Std

namespace OrderedParityCovers

def parity : List Bool → Bool
  | [] => false
  | x :: xs => x ^^ parity xs

def oddLength {α : Type} : List α → Bool
  | [] => false
  | _ :: xs => !oddLength xs

theorem parityShift (xs : List Bool) (q : Bool) :
    parity (xs.map fun x => x ^^ q) = (parity xs ^^ (q && oddLength xs)) := by
  induction xs with
  | nil => simp [parity, oddLength]
  | cons x xs ih =>
    simp only [List.map_cons, parity, oddLength, ih]
    cases x <;> cases q <;> cases parity xs <;> cases oddLength xs <;> rfl

/-- Multiplication by I+J over the binary field. -/
def shiftByParity (xs : List Bool) := xs.map fun x => x ^^ parity xs

theorem shiftTwice (xs : List Bool) (even : oddLength xs = false) :
    shiftByParity (shiftByParity xs) = xs := by
  unfold shiftByParity
  rw [parityShift, even]
  simp only [Bool.and_false, Bool.xor_false, List.map_map]
  have cancel : ((fun x : Bool => x ^^ parity xs) ∘ (fun x => x ^^ parity xs)) = id := by
    funext y
    cases y <;> cases parity xs <;> rfl
  simp [cancel]

theorem parityCoverSound {A I : Type} (rows : List I) (fail weight : I → A → Bool)
    (cover : ∀ x, parity (rows.map fun i => fail i x && weight i x) = true) :
    ¬ ∃ x, ∀ i ∈ rows, fail i x = false := by
  rintro ⟨x, hx⟩
  have noCharge : ∀ rs : List I, (∀ i ∈ rs, fail i x = false) →
      parity (rs.map fun i => fail i x && weight i x) = false := by
    intro rs
    induction rs with
    | nil => simp [parity]
    | cons i rs ih =>
      intro h
      have hi := h i List.mem_cons_self
      have hr := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
      simp [parity, hi, hr]
  have zero := noCharge rows hx
  rw [cover x] at zero
  contradiction

end OrderedParityCovers
