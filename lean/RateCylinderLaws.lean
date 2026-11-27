import Std

namespace RateCylinderLaws

/-- If t is a ticket's index within its cell, its rank block ends
    below that cell's total rank capacity. -/
theorem ticketRankFits (t slots width u : Nat)
    (inCell : t < slots) (raw : u < width) :
    t * width + u < slots * width := by
  calc
    t * width + u < t * width + width := Nat.add_lt_add_left raw _
    _ = (t+1) * width := (Nat.succ_mul _ _).symm
    _ ≤ slots * width := Nat.mul_le_mul_right _ inCell

/-- Two different tickets in one cell have disjoint rank blocks. -/
theorem orderedTicketRanks (t t' width u u' : Nat)
    (ordered : t < t') (raw : u < width) :
    t * width + u < t' * width + u' := by
  have h := ticketRankFits t t' width u ordered raw
  omega

/-- With an integer common denominator den, each cell loses at most
    3*den target units to conservative ticket rounding. -/
theorem totalRoundingLoss (cells : List (Nat × Nat)) (den : Nat)
    (each : ∀ qr ∈ cells, qr.1 ≤ qr.2 * den + 3 * den) :
    (cells.map Prod.fst).sum ≤ (cells.map Prod.snd).sum * den + cells.length * (3 * den) := by
  induction cells with
  | nil => simp
  | cons x xs ih =>
    have head := each x (by simp)
    have tail := ih (fun y hy => each y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
      Nat.succ_mul] at *
    omega

end RateCylinderLaws
