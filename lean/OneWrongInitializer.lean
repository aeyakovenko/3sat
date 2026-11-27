import Std

namespace OneWrongInitializer

inductive Address where
  | key (x : Nat)
  | dummy (i : Nat)
  deriving DecidableEq

abbrev Memory := Address → Bool
abbrev Event := Bool × Bool

def mark (m : Memory) (a : Address) : Memory := fun b => if b = a then true else m b

/-- An event records the loaded bit and the previous bit at the store target.
The previous store bit is an observation in this definition, not a machine load. -/
def run (m : Memory) (i : Nat) (found : Bool) : List Nat → List Event
  | [] => []
  | x :: xs =>
    let reply := m (if found then .dummy i else .key x)
    let next := found || reply
    let target := if next then .dummy i else .key x
    (reply, m target) :: run (mark m target) (i+1) next xs

def Fresh (m : Memory) (i : Nat) := ∀ j, i ≤ j → m (.dummy j) = false

private theorem fresh_step {m : Memory} {i : Nat} (f : Fresh m i) (x : Nat) :
    Fresh (mark m (.dummy i)) (i+1) ∧ Fresh (mark m (.key x)) (i+1) := by
  constructor
  · intro j hj
    have h : j ≠ i := by omega
    simp [mark, h, f j (by omega)]
  · intro j hj
    simp [mark, f j (by omega)]

private theorem locked (xs : List Nat) (m : Memory) (i : Nat) (f : Fresh m i) :
    run m i true xs = List.replicate xs.length (false,false) := by
  induction xs generalizing m i with
  | nil => rfl
  | cons x xs ih =>
    simp [run, f i (by omega), ih _ _ ((fresh_step f x).1), List.replicate_succ]

def Clean (m : Memory) (xs : List Nat) := xs.Nodup ∧ ∀ x ∈ xs, m (.key x) = false

private theorem clean_step (m : Memory) (x : Nat) (xs : List Nat) :
    Clean m (x :: xs) ↔ m (.key x) = false ∧ Clean (mark m (.key x)) xs := by
  simp only [Clean, List.nodup_cons]
  constructor
  · rintro ⟨⟨hx, hn⟩, h⟩
    refine ⟨h x (by simp), hn, ?_⟩
    intro y hy
    have hxy : y ≠ x := fun e => hx (e ▸ hy)
    simp [mark, hxy, h y (by simp [hy])]
  · rintro ⟨hx, hn, h⟩
    refine ⟨⟨?_, hn⟩, ?_⟩
    · intro hmem
      simpa [mark] using h x hmem
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · by_cases he : y = x
        · simpa [he] using hx
        · simpa [mark, he] using h y hy

/-- Every store target is fresh, and the complete word-reply stream has at
most one true bit. It has none exactly for a list disjoint from the initial
real marks and without repeated keys. -/
theorem mark_scan (xs : List Nat) (m : Memory) (i : Nat) (f : Fresh m i) :
    (∀ e ∈ run m i false xs, e.2 = false) ∧
    ((run m i false xs).map Prod.fst).count true ≤ 1 ∧
    (((run m i false xs).map Prod.fst).count true = 0 ↔ Clean m xs) := by
  induction xs generalizing m i with
  | nil => simp [run, Clean]
  | cons x xs ih =>
    rw [clean_step]
    cases h : m (.key x) with
    | false =>
      simpa [run, h] using ih (mark m (.key x)) (i+1) ((fresh_step f x).2)
    | true =>
      simp [run, h, f i (by omega), locked xs _ _ ((fresh_step f x).1), List.count_replicate]

/-- From zero initialization, the proposed all-zero stream is correct exactly
on element-distinctness inputs. The one-error promise holds on every list. -/
theorem from_zero (xs : List Nat) :
    let records := run (fun _ => false) 0 false xs
    (∀ e ∈ records, e.2 = false) ∧
    (records.map Prod.fst).count true ≤ 1 ∧
    ((records.map Prod.fst).count true = 0 ↔ xs.Nodup) := by
  simpa [Clean] using mark_scan xs (fun _ => false) 0 (fun _ _ => rfl)

end OneWrongInitializer
