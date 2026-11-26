import Std

namespace GreedyFieldDigits

/-- Divisibility prevents a sorted list of powers from stepping past a
    divisible target. This is the exchange used both to fold exponents
    modulo X^Q-X and to prove optimality for mixed slot capacities. -/
theorem exact_prefix (coins : List Nat) (target : Nat)
    (chain : coins.Pairwise (fun a b => b ∣ a))
    (divides : ∀ b ∈ coins, b ∣ target) (enough : target ≤ coins.sum) :
    ∃ front rest, coins = front ++ rest ∧ front.sum = target := by
  induction coins generalizing target with
  | nil =>
    simp at enough
    exact ⟨[], [], rfl, by simpa using enough.symm⟩
  | cons a coins ih =>
    by_cases hz : target = 0
    · exact ⟨[], _, rfl, by simp [hz]⟩
    have ha := Nat.le_of_dvd (show 0 < target by omega) (divides a (by simp))
    obtain ⟨ahead, tailChain⟩ := List.pairwise_cons.mp chain
    have subDiv : ∀ b ∈ coins, b ∣ target - a := fun b hb =>
      Nat.dvd_sub (divides b (by simp [hb])) (ahead b hb)
    simp only [List.sum_cons] at enough
    obtain ⟨front, rest, er, ef⟩ := ih (target-a) tailChain subDiv (by omega)
    exact ⟨a :: front, rest, by simp [er], by simp only [List.sum_cons, ef]; omega⟩

/-- The low digits are supplied in descending order of their place values. -/
def value (q : Nat) : List Nat → Nat
  | [] => 0
  | b :: ds => b * q ^ ds.length + value q ds

def fill (q : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, budget =>
    let take := min (q-1) budget
    take * q ^ k + fill q k (budget-take)

theorem value_lt {q : Nat} (_hq : 1 < q) (ds : List Nat)
    (hd : ∀ x ∈ ds, x < q) : value q ds < q ^ ds.length := by
  induction ds with
  | nil => simp [value]
  | cons b ds ih =>
    have hb := hd b (by simp)
    have tail := ih (fun x hx => hd x (by simp [hx]))
    have step := Nat.mul_le_mul_right (q ^ ds.length) (show b+1 ≤ q by omega)
    simp only [Nat.add_one_mul] at step
    simpa only [value, List.length_cons, Nat.pow_succ, Nat.mul_comm (q ^ ds.length) q]
      using (show b * q ^ ds.length + value q ds < q * q ^ ds.length by omega)

/-- If the leading digit is capacity-limited, filling it before all the
    lower digits maximizes the integer over every affordable digit list. -/
theorem leading_bound {q cap budget b : Nat} (hq : 1 < q) (ds : List Nat)
    (digits : ∀ x ∈ ds, x < q) (hbcap : b ≤ cap) (cost : b + ds.sum ≤ budget)
    (tailBound : b = min cap budget →
      value q ds ≤ fill q ds.length (budget - min cap budget)) :
    b * q ^ ds.length + value q ds ≤
      min cap budget * q ^ ds.length + fill q ds.length (budget - min cap budget) := by
  let a := min cap budget
  have hba : b ≤ a := Nat.le_min.mpr ⟨hbcap, by omega⟩
  by_cases h : b = a
  · have ht := tailBound h
    rw [show b = min cap budget from h]
    omega
  · have hstep := Nat.mul_le_mul_right (q ^ ds.length) (show b+1 ≤ a by omega)
    simp only [Nat.add_one_mul] at hstep
    have hv := value_lt hq ds digits
    change _ ≤ a * q ^ ds.length + _
    omega

theorem fill_max {q : Nat} (hq : 1 < q) (ds : List Nat) (budget : Nat)
    (digits : ∀ x ∈ ds, x < q) (cost : ds.sum ≤ budget) :
    value q ds ≤ fill q ds.length budget := by
  induction ds generalizing budget with
  | nil => simp [value, fill]
  | cons b ds ih =>
    have htail : ∀ x ∈ ds, x < q := fun x hx => digits x (by simp [hx])
    have hb := digits b (by simp)
    simp only [List.sum_cons] at cost
    simp only [value, List.length_cons, fill]
    apply leading_bound hq ds htail (by omega) cost
    intro he
    exact ih _ htail (by omega)

theorem capped_digits_max {q cap budget top : Nat} (hq : 1 < q)
    (ds : List Nat) (hd : ∀ x ∈ ds, x < q) (ht : top ≤ cap)
    (hc : top + ds.sum ≤ budget) :
    top * q ^ ds.length + value q ds ≤
      min cap budget * q ^ ds.length + fill q ds.length (budget - min cap budget) := by
  apply leading_bound hq ds hd ht hc
  intro he
  exact fill_max hq ds _ hd (by omega)

end GreedyFieldDigits
