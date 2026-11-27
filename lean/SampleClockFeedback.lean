import Std

namespace SampleClockFeedback

/-- A breadth-first exploration removes one pending vertex and inserts its children. -/
inductive Scan : Nat → List Nat → Nat → Prop where
  | stop (pending : Nat) : Scan pending [] pending
  | step {rest children final : Nat} {tail : List Nat} :
      Scan (rest + children) tail final → Scan (rest + 1) (children :: tail) final

theorem queueBalance {start final : Nat} {counts : List Nat}
    (run : Scan start counts final) :
    start + counts.sum = counts.length + final := by
  induction run with
  | stop => simp
  | step tail ih =>
    simp only [List.sum_cons, List.length_cons]
    omega

/-- If a further vertex can be explored, the previous vertices have at least as
    many children in total as there were explored vertices. -/
theorem offspringTotal {final : Nat} {counts : List Nat}
    (run : Scan 1 counts final) (more : 0 < final) :
    counts.length ≤ counts.sum := by
  have h := queueBalance run
  omega

/-- On a common integer probability scale, if every conditional first-mismatch
    charge is at most e, the sum over all r opportunities is at most r*e. -/
theorem firstMismatch (charges : List Nat) (e : Nat)
    (bound : ∀ n ∈ charges, n ≤ e) : charges.sum ≤ charges.length * e := by
  induction charges with
  | nil => simp
  | cons a xs ih =>
    have head := bound a (by simp)
    have tail := ih (fun x hx => bound x (by simp [hx]))
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- Scaled mass from one already-published branch dominates the desired
    coordinate, up to its launch weight times the distribution error. -/
theorem earlyCoordinate (mu launch actual predicted error : Nat)
    (issued : launch * actual ≤ mu)
    (coupled : predicted ≤ actual + error) :
    launch * predicted ≤ mu + launch * error := by
  have h := Nat.mul_le_mul_left launch coupled
  rw [Nat.mul_add] at h
  omega

/-- A literal floor absorbs a small uniform error coordinatewise. -/
theorem relativeFloor (new early error factor : Nat)
    (absolute : new ≤ early + error) (floorBound : factor * error ≤ early) :
    factor * new ≤ (factor + 1) * early := by
  have h := Nat.mul_le_mul_left factor absolute
  rw [Nat.mul_add] at h
  rw [Nat.add_mul, Nat.one_mul]
  omega

end SampleClockFeedback
