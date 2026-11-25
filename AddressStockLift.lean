import Std

namespace AddressStockLift

/-- `generated` counts distinct needed addresses with a charged first
    production. Their producing instructions and the m original loads are
    disjoint in the separate-operation ISA. `literals` counts distinct
    literal residues, so repetitions do not earn additional credit. -/
structure Stock (m time initial metadata literals generated slots : Nat) : Prop where
  cover : m ≤ initial + metadata + literals + generated
  disjoint : m + generated ≤ time
  literalBudget : literals ≤ 2 * slots

theorem cost_bounds (h : Stock m T h₀ r literals generated C) :
    m + (m - (h₀ + r + literals)) ≤ T ∧ 2*m ≤ T + (h₀ + r + 2*C) := by
  obtain ⟨cover, disjoint, budget⟩ := h
  omega

/-- At a deadline p*m/q the gap times the number of marked addresses must
    be covered by the initial palette, metadata and distinct literals. -/
theorem fast_needs_literals (h : Stock m T h₀ r literals generated C)
    (rate : p + gap = 2*q) (fast : q*T ≤ p*m) :
    gap*m ≤ q*(h₀ + r + literals) := by
  obtain ⟨cover, disjoint, _⟩ := h
  have scaled := Nat.mul_le_mul_left q (show 2*m ≤ T + (h₀+r+literals) by omega)
  have factor : q*(2*m) = p*m + gap*m := by
    rw [← Nat.add_mul, rate]
    ac_rfl
  rw [factor, Nat.mul_add] at scaled
  omega

theorem strict_failure (h : Stock m T h₀ r literals generated C)
    (rate : p + gap = 2*q) (margin : q*(h₀+r+2*C) < gap*m) : p*m < q*T := by
  apply Classical.byContradiction
  intro slow
  have need := fast_needs_literals h rate (by omega)
  have cap := Nat.mul_le_mul_left q (Nat.add_le_add_left h.literalBudget (h₀+r))
  omega

/-- With `gap = 2*q-p > 0`, this is ceiling(2/(2-p/q)). -/
def additionalCells (q gap : Nat) := (2*q + gap - 1) / gap

theorem enough_additional (q gap : Nat) (positive : 0 < gap) :
    2*q ≤ gap * additionalCells q gap := by
  unfold additionalCells
  have rem := Nat.mod_lt (2*q + gap - 1) positive
  have split := Nat.mod_add_div (2*q + gap - 1) gap
  omega

/-- Any realizable marked count above the rounded increment suffices,
    including when changing word width skips an intermediate count. -/
theorem successor_margin (margin : q*(h₀+r+2*C) < gap*m) (positive : 0 < gap)
    (larger : m + additionalCells q gap ≤ m') :
    q*(h₀+r+2*(C+1)) < gap*m' := by
  have enough := enough_additional q gap positive
  have grow := Nat.mul_le_mul_left gap larger
  rw [Nat.mul_add] at grow
  have step : q*(h₀+r+2*(C+1)) = q*(h₀+r+2*C) + 2*q := by
    rw [show h₀+r+2*(C+1) = (h₀+r+2*C)+2 by omega, Nat.mul_add, Nat.mul_comm q 2]
  omega

/-- No syntactic relationship between the old and the new program occurs
    in this step: only the cap on the new program and the old strict margin. -/
theorem successor_clock (newRun : Stock m' T h₀ r literals generated (C+1))
    (subcritical : p < 2*q) (margin : q*(h₀+r+2*C) < (2*q-p)*m)
    (larger : m + additionalCells q (2*q-p) ≤ m') : p*m' < q*T := by
  exact strict_failure newRun (show p+(2*q-p) = 2*q by omega)
    (successor_margin margin (by omega) larger)

/-- Charging the bit lengths of distinct literal spellings individually:
    all but at most `short` spellings each contribute at least `b` bits. -/
theorem literal_text (lengths : List Nat) (b short : Nat)
    (few : (lengths.filter (fun k => decide (k < b))).length ≤ short) :
    b * (lengths.length - short) ≤ lengths.sum := by
  have bound : b * (lengths.length - (lengths.filter (fun k => decide (k < b))).length)
      ≤ lengths.sum := by
    clear few
    induction lengths with
    | nil => simp
    | cons k rest ih =>
      have le := List.length_filter_le (fun k => decide (k < b)) rest
      by_cases small : k < b
      · simpa [small] using Nat.le_trans ih (Nat.le_add_left _ k)
      · simp only [List.length_cons, List.filter_cons, decide_eq_true_eq, small, if_false,
          List.sum_cons]
        rw [show rest.length + 1 - (List.filter (fun k => decide (k < b)) rest).length =
            (rest.length - (List.filter (fun k => decide (k < b)) rest).length) + 1 by omega,
          Nat.mul_add, Nat.mul_one]
        omega
  exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left few _)) bound

end AddressStockLift
