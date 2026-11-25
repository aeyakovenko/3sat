import Std

namespace SparseDecimalNames

/-- For a field fragment the first coordinate counts bytes and the second
counts sign and binary-digit locations that can vary across source clauses. -/
theorem window_capacity (t : Nat) (chunks : List (Nat × Nat))
    (one : ∀ v ∈ chunks, t * v.2 ≤ v.1 + 2*t) :
    t * (chunks.map Prod.snd).sum ≤
      (chunks.map Prod.fst).sum + chunks.length * (2*t) := by
  induction chunks with
  | nil => simp
  | cons a rest ih =>
    have head := one a (by simp)
    have tail := ih (fun v hv => one v (by simp [hv]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have len : (rest.length+1)*(2*t) = rest.length*(2*t)+2*t := Nat.succ_mul _ _
    rw [len, Nat.mul_add]
    omega

/-- The quasilinear-length reduction and polylogarithmic simulator can use
the strict margins between the native exponents and the FLMV thresholds. -/
theorem explicit_slack :
    6 * 1000 < 5 * 1201 ∧
    (5 + 2*16) * 1000 < 464 * 80 ∧
    464 < 509 ∧
    (2*509 + 1201) * 1201^2 < 3201 * 1000^2 := by
  decide

end SparseDecimalNames
