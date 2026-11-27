import Std

namespace PhysicalBitCarrier

/-- The two fixed clauses which connect the names that differ in one bit. -/
def opposite (lo hi : Bool) : Bool := (lo || hi) && (!lo || !hi)

/-- The two other literals of the selected record have been forced false. -/
def carrier (raw lo hi : Bool) : Bool :=
  opposite lo hi && (if raw then hi else lo)

theorem name_bit_exact (raw lo hi : Bool) :
    carrier raw lo hi = true ↔ lo = !raw ∧ hi = raw := by
  cases raw <;> cases lo <;> cases hi <;> decide

/-- All pins can be enforced at once, with independent pairs. A checker may
    be any Boolean predicate on the high-name signals. -/
theorem simultaneous {I : Type} (raw : I → Bool) (checker : (I → Bool) → Prop) :
    (∃ lo hi : I → Bool, (∀ i, carrier (raw i) (lo i) (hi i) = true) ∧ checker hi)
    ↔ checker raw := by
  constructor
  · rintro ⟨lo, hi, valid, witness⟩
    have eq : hi = raw := funext (fun i => ((name_bit_exact _ _ _).mp (valid i)).2)
    exact eq ▸ witness
  · intro witness
    exact ⟨fun i => !(raw i), raw, fun _ => (name_bit_exact _ _ _).mpr ⟨rfl, rfl⟩, witness⟩

/-- If no surviving record contained a usable bit then that record would
    add zero to this count. Each used record contributes at most the stride. -/
theorem bits_vs_records (counts : List Nat) (stride : Nat)
    (bound : ∀ k ∈ counts, k ≤ stride) :
    counts.sum ≤ (counts.filter (fun k => k > 0)).length * stride := by
  induction counts with
  | nil => simp
  | cons k ks ih =>
    have tail := ih (fun j hj => bound j (List.mem_cons_of_mem _ hj))
    have head := bound k (by simp)
    cases k with
    | zero => simpa using tail
    | succ j =>
      simp only [List.sum_cons, List.filter_cons, decide_eq_true_eq, Nat.zero_lt_succ,
        if_true, List.length_cons, Nat.succ_mul]
      omega

end PhysicalBitCarrier
