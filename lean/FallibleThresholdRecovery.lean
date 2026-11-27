import Std

namespace FallibleThresholdRecovery

inductive Certificate where
  | empty
  | jump (point : Nat)

/-- Threshold t covers the assignments numbered strictly below t. -/
def Matches (reply : Nat → Bool) (size : Nat) : Certificate → Prop
  | .empty => reply size = false
  | .jump j => j < size ∧ reply j = false ∧ reply (j+1) = true

def Verified (W : Nat → Prop) (size : Nat) : Certificate → Prop
  | .empty => False
  | .jump j => j < size ∧ W j

theorem jump_exists (bits : Nat → Bool) (start : bits 0 = false) (n : Nat)
    (last : bits n = true) : ∃ j < n, bits j = false ∧ bits (j+1) = true := by
  induction n with
  | zero => simp [start] at last
  | succ n ih =>
    cases h : bits n with
    | false => exact ⟨n, by omega, h, last⟩
    | true =>
      obtain ⟨j, hj, old, new⟩ := ih h
      exact ⟨j, by omega, old, new⟩

/-- No monotonicity is required of the majority or of an untrusted reply row. -/
theorem certificate_exists (bits : Nat → Bool) (start : bits 0 = false) (n : Nat) :
    ∃ c, Matches bits n c := by
  cases h : bits n with
  | false => exact ⟨.empty, h⟩
  | true =>
    obtain ⟨j, hj, old, new⟩ := jump_exists bits start n h
    exact ⟨.jump j, hj, old, new⟩

/-- Verifying the chosen points decides existence if one row answers all
    initial-segment queries truthfully. All the other rows can be arbitrary. -/
theorem truthful_row_decides {ι : Type} (W : Nat → Prop) (size : Nat)
    (reply : ι → Nat → Bool) (cert : ι → Certificate)
    (certified : ∀ i, Matches (reply i) size (cert i))
    (truth : ∃ i, ∀ t ≤ size, reply i t = true ↔ ∃ j < t, W j) :
    (∃ i, Verified W size (cert i)) ↔ ∃ j < size, W j := by
  constructor
  · rintro ⟨i, h⟩
    cases hc : cert i with
    | empty => simp [hc, Verified] at h
    | jump j =>
      obtain ⟨hj, yes⟩ := (show j < size ∧ W j by simpa [hc, Verified] using h)
      exact ⟨j, hj, yes⟩
  · intro yes
    obtain ⟨i, exactReply⟩ := truth
    have h := certified i
    refine ⟨i, ?_⟩
    cases hc : cert i with
    | empty =>
      have no : reply i size = false := by simpa [hc, Matches] using h
      have accept := (exactReply size (Nat.le_refl _)).mpr yes
      rw [no] at accept
      contradiction
    | jump j =>
      obtain ⟨hj, old, new⟩ :=
        (show j < size ∧ reply i j = false ∧ reply i (j+1) = true by
          simpa [hc, Matches] using h)
      obtain ⟨u, hu, witness⟩ := (exactReply (j+1) (by omega)).mp new
      have notBefore : ¬ u < j := by
        intro before
        have nonempty := (exactReply j (by omega)).mpr ⟨u, before, witness⟩
        rw [old] at nonempty
        contradiction
      have same : u = j := by omega
      exact ⟨hj, same ▸ witness⟩

/-- Count failed predicted certificates. Compatible tables can also be
    discarded by successful probes, which the following inequalities permit. -/
theorem halving_bound (count : Nat → Nat) (half : ∀ i, 2 * count (i+1) ≤ count i)
    (rounds : Nat) : 2^rounds * count rounds ≤ count 0 := by
  induction rounds with
  | zero => simp
  | succ k ih =>
    calc
      2^(k+1) * count (k+1) = 2^k * (2 * count (k+1)) := by
        simp [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ 2^k * count k := Nat.mul_le_mul_left _ (half k)
      _ ≤ count 0 := ih

/-- One independent bucket. A subset answer keeps at least half its live
    candidates; a negative point test removes at most one. -/
inductive BucketTrace (size : Nat) : Nat → Nat → Nat → Prop where
  | start : BucketTrace size size 0 0
  | subset {x a v} (prior : BucketTrace size x a v) (y : Nat) (half : x ≤ 2*y) :
      BucketTrace size y (a+1) v
  | point {x a v} (prior : BucketTrace size x a v) (y : Nat) (one : x ≤ y+1) :
      BucketTrace size y a (v+1)

theorem bucket_capacity {m r a v : Nat} (trace : BucketTrace m r a v) :
    m ≤ 2^a * (r+v) := by
  induction trace with
  | start => simp
  | @subset x a v prev y half ih =>
    calc
      m ≤ 2^a * (x+v) := ih
      _ ≤ 2^a * (2*(y+v)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2^(a+1)*(y+v) := by simp [Nat.pow_succ, Nat.mul_assoc]
  | @point x a v prev y one ih =>
    exact Nat.le_trans ih (Nat.mul_le_mul_left _ (by omega))

end FallibleThresholdRecovery
