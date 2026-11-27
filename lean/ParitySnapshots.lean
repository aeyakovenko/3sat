import Std

namespace ParitySnapshots

/-- Every membership lookup on the observed positions is correct if the
    stored positives are observed and the hash separates observed points. -/
theorem lookup_agrees {ι κ : Type} (f : ι → κ) (observed positive : List ι)
    (inside : ∀ x ∈ positive, x ∈ observed)
    (separate : ∀ x ∈ observed, ∀ y ∈ observed, f x = f y → x = y)
    (x : ι) (hx : x ∈ observed) : f x ∈ positive.map f ↔ x ∈ positive := by
  constructor
  · intro h
    obtain ⟨y, hy, hit⟩ := List.mem_map.mp h
    have eq := separate y (inside y hy) x hx hit
    simpa [← eq] using hy
  · intro h
    exact List.mem_map.mpr ⟨x, h, rfl⟩

/-- Each nonempty relative test on a pointer inspects only one bit of the
    coordinatewise XOR of its query strings. -/
def xorWords {ι : Type} (xs : List (ι → Bool)) : ι → Bool :=
  match xs with
  | [] => fun _ => false
  | x :: tail => fun j => xor (x j) (xorWords tail j)

def xorBits : List Bool → Bool
  | [] => false
  | b :: tail => xor b (xorBits tail)

theorem relative_pointer {ι : Type} (xs : List (ι → Bool)) (j : ι) :
    xorBits (xs.map (fun x => x j)) = xorWords xs j := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp [xorBits, xorWords, ih]

/-- A specific other pointer is excluded by equality of two responses on
    the zero vector and the unit vector at that index. -/
theorem pair_excludes [DecidableEq ι] (j k : ι) :
    (fun _ : ι => false) j = (fun i : ι => decide (i = k)) j ↔ j ≠ k := by
  by_cases h : j = k <;> simp [h]

end ParitySnapshots
