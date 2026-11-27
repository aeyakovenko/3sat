import Std

namespace FullCubeSelection

private theorem unionCount (tables : List Nat) (advice : List A) (miss : A → Nat → Bool)
    (m : Nat) (each : ∀ a ∈ advice, tables.countP (miss a) ≤ m) :
    tables.countP (fun h => advice.any (fun a => miss a h)) ≤ advice.length*m := by
  induction advice with
  | nil => simp
  | cons a as ih =>
    let rest := fun h => as.any (fun z => miss z h)
    have join : tables.countP (fun h => miss a h || rest h) ≤
        tables.countP (miss a) + tables.countP rest := by
      clear each ih
      induction tables with
      | nil => simp
      | cons t ts rec =>
        cases p : miss a t <;> cases q : rest t <;> simp [List.countP_cons, p,q] <;> omega
    have first := each a (by simp)
    have tail := ih (fun z hz => each z (by simp [hz]))
    simpa [List.any_cons, Nat.succ_mul, Nat.add_comm, rest] using
      Nat.le_trans join (Nat.add_le_add first tail)

/-- Equal probability sample tables may be listed with multiplicity. Each
    advice spoils at most m of them, with no independence across advice. -/
theorem commonTable (tables : List Nat) (advice : List A) (miss : A → Nat → Bool)
    (m : Nat) (each : ∀ a ∈ advice, tables.countP (miss a) ≤ m)
    (small : advice.length*m < tables.length) :
    ∃ h ∈ tables, ∀ a ∈ advice, miss a h = false := by
  apply Classical.byContradiction
  intro noneGood
  have cover : tables.countP (fun h => advice.any (fun a => miss a h)) = tables.length := by
    apply List.countP_eq_length.mpr
    intro h hh
    cases hit : advice.any (fun a => miss a h) with
    | true => rfl
    | false =>
      exfalso
      apply noneGood
      refine ⟨h,hh,?_⟩
      intro a ha
      cases hm : miss a h with
      | false => rfl
      | true =>
        have yes := List.any_eq_true.mpr (show ∃ z ∈ advice, miss z h = true from ⟨a,ha,hm⟩)
        simp [hit] at yes
  have bound := unionCount tables advice miss m each
  omega

/-- Equal-width binary table codes in numeric order are in lexicographic
    order. Qualification may be an arbitrary predicate on these codes. -/
def first (good : Nat → Prop) (h : Nat) : Prop := good h ∧ ∀ j < h, ¬good j

private theorem someFirst (good : Nat → Prop) (b : Nat) (hb : good b) : ∃ h, first good h := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases earlier : ∃ j < b, good j
    · obtain ⟨j,lt,yes⟩ := earlier
      exact ih j lt yes
    · exact ⟨b,hb,fun j hj g => earlier ⟨j,hj,g⟩⟩

private theorem firstUnique (x y : Nat) (hx : first good x) (hy : first good y) : x = y := by
  have notLT : ¬x < y := fun lt => hy.2 x lt hx.1
  have notGT : ¬y < x := fun lt => hx.2 y lt hy.1
  omega

/-- Every pointwise existential bit query may quantify a fresh table, yet
    one common least table supplies every bit of every indexed member. -/
theorem allIndexedBits (good : Nat → Prop) (existsGood : ∃ h, good h)
    (bit : Nat → I → J → Bool) :
    ∃ h, first good h ∧ ∀ i j,
      ((∃ table, first good table ∧ bit table i j = true) ↔ bit h i j = true) := by
  obtain ⟨b,hb⟩ := existsGood
  obtain ⟨h,firstH⟩ := someFirst good b hb
  refine ⟨h,firstH,fun i j => ⟨?_,fun v => ⟨h,firstH,v⟩⟩⟩
  rintro ⟨table,firstT,v⟩
  exact firstUnique table h firstT firstH ▸ v

/-- All binary names of length at most r, including the empty name. -/
def nameCount : Nat → Nat
  | 0 => 1
  | r+1 => nameCount r + 2^(r+1)

theorem exactCapacity (r : Nat) : nameCount r + 1 = 2^(r+1) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change nameCount r + 2^(r+1) + 1 = 2^((r+1)+1)
    rw [Nat.pow_succ 2 (r+1)]
    omega

theorem lessThanHalf (r printed : Nat) (cap : printed ≤ nameCount r) :
    2*printed < 2^(r+2) := by
  have h := exactCapacity r
  rw [show r+2 = (r+1)+1 by omega, Nat.pow_succ]
  omega

end FullCubeSelection
