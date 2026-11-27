import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset

namespace BalancedRowCertificates

open Finset

/-- Exact finite cell sampling. A query may prescribe any set of at most `d`
    addresses. Some fixed-size sample covers at least the mean number of queries,
    with the denominator cleared on the right. -/
theorem some_sample_covers_at_least_average {A I : Type*} [DecidableEq A]
    (cells : Finset A) (Q : Finset I) (need : I → Finset A) (d : ℕ)
    (hd : d ≤ cells.card) (inside : ∀ i ∈ Q, need i ⊆ cells)
    (small : ∀ i ∈ Q, (need i).card ≤ d) :
    ∃ sample ∈ cells.powersetCard d,
      (∑ i ∈ Q, (cells.card - (need i).card).choose (d - (need i).card)) ≤
        cells.card.choose d * (Q.filter (fun i => need i ⊆ sample)).card := by
  classical
  let samples := cells.powersetCard d
  let covered (sample : Finset A) := (Q.filter (fun i => need i ⊆ sample)).card
  have incident : (∑ s ∈ samples, covered s) =
      ∑ i ∈ Q, (cells.card - (need i).card).choose (d - (need i).card) := by
    calc
      _ = ∑ i ∈ Q, (samples.filter (fun s => need i ⊆ s)).card := by
        simp only [covered, card_filter]
        rw [sum_comm]
      _ = _ := sum_congr rfl fun i hi =>
        card_filter_powersetCard_subset (need i) cells d (inside i hi) (small i hi)
  have ex : samples.Nonempty := powersetCard_nonempty.mpr hd
  obtain ⟨s, hs, hm⟩ := samples.exists_max_image covered ex
  refine ⟨s, hs, incident.symm.trans_le ?_⟩
  calc
    _ ≤ ∑ _x ∈ samples, covered s := sum_le_sum hm
    _ = _ := by simp [samples, covered]

/-- Every member of a family of row queries lies in the box of its row projections. -/
private theorem card_le_projection_product {k B : ℕ} (Q : Finset (Fin k → Fin B)) :
    Q.card ≤ ∏ j, (Q.image (fun q => q j)).card := by
  classical
  rw [← Fintype.card_piFinset]
  exact card_le_card fun q hq => Fintype.mem_piFinset.mpr fun j => mem_image_of_mem _ hq

/-- A family with at least `a^k` queries reveals at least `k*a` different
    row/column entries. This estimate is sharp for a Cartesian product. -/
theorem many_queries_reveal_many_entries {k B a : ℕ} (Q : Finset (Fin k → Fin B))
    (many : a ^ k ≤ Q.card) : k * a ≤ ∑ j, (Q.image (fun q => q j)).card := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  let u (j : Fin k) : ℝ := (Q.image (fun q => q j)).card
  have ha' : 0 < (a : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ha
  have prod_ge : (a : ℝ)^k ≤ ∏ j, u j := by
    dsimp [u]
    exact_mod_cast many.trans (card_le_projection_product Q)
  have prod_norm : 1 ≤ ∏ j, u j / (a : ℝ) := by
    rw [prod_div_distrib, prod_const, card_univ, Fintype.card_fin]
    exact (one_le_div (pow_pos ha' k)).mpr prod_ge
  have bound : (∏ j, u j / (a : ℝ)) ≤ Real.exp (∑ j, (u j / a - 1)) := by
    rw [Real.exp_sum]
    apply prod_le_prod₀
    · intro j _
      exact div_nonneg (Nat.cast_nonneg _) ha'.le
    · intro j _
      simpa using Real.add_one_le_exp (u j / (a : ℝ) - 1)
  have nonneg : 0 ≤ ∑ j, (u j / (a : ℝ) - 1) := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_zero]
    exact prod_norm.trans bound
  simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, sub_nonneg] at nonneg
  simp only [div_eq_mul_inv, ← sum_mul] at nonneg
  rw [← div_eq_mul_inv] at nonneg
  have cardinal : (k : ℝ) * a ≤ ∑ j, u j := (le_div_iff₀ ha').mp nonneg
  dsimp [u] at cardinal
  exact_mod_cast cardinal

/-- The transcript identifies the value at every coordinate in its projections. -/
theorem projection_entry_true {k B : ℕ} (Q : Finset (Fin k → Fin B))
    (db : Fin k → Fin B → Bool) (cert : ∀ q ∈ Q, ∀ j, db j (q j) = true)
    (j : Fin k) {b : Fin B} (hb : b ∈ Q.image (fun q => q j)) : db j b = true := by
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hb
  exact cert q hq j

#print axioms some_sample_covers_at_least_average
#print axioms many_queries_reveal_many_entries
#print axioms projection_entry_true

end BalancedRowCertificates
