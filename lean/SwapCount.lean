import Std

namespace SwapCount

private theorem length_le_of_nodup_subset {K : Type} [DecidableEq K]
    (xs ys : List K) (distinct : xs.Nodup) (inside : ∀ a ∈ xs, a ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp distinct
    have hy : x ∈ ys := inside x (by simp)
    have hpos : 0 < ys.length := List.length_pos_of_mem hy
    have htail := ih (ys.erase x) tail (by
      intro a ha
      have hne : a ≠ x := fun h => fresh (h ▸ ha)
      exact (List.mem_erase_of_ne hne).2 (inside a (by simp [ha])))
    rw [List.length_erase_of_mem hy] at htail
    simp
    omega

/-- Membership of a color in the palette of an inclusive interval. -/
def InPalette {V K : Type} (le : V → V → Prop) (label : V → K)
    (a b : V) (code : K) : Prop :=
  ∃ x, le a x ∧ le x b ∧ label x = code

/-- Interval excess is superadditive in a ranked poset with different labels
    on strictly comparable elements. Input lists enumerate the three palettes,
    and u and v are the rank differences of the two component intervals. -/
theorem palette_excess_superadditive {V K : Type} [DecidableEq K]
    (le : V → V → Prop) (label : V → K) (refl : ∀ x, le x x)
    (trans : ∀ {x y z}, le x y → le y z → le x z)
    (antisym : ∀ {x y}, le x y → le y x → x = y)
    (proper : ∀ {x y}, le x y → label x = label y → x = y)
    (a b c : V) (ab : le a b) (bc : le b c)
    (lower upper outer : List K) (loDistinct : lower.Nodup) (upDistinct : upper.Nodup)
    (loEnum : ∀ k, k ∈ lower ↔ InPalette le label a b k)
    (upEnum : ∀ k, k ∈ upper ↔ InPalette le label b c k)
    (outEnum : ∀ k, k ∈ outer ↔ InPalette le label a c k)
    (u v : Nat) (loRanks : u+1 ≤ lower.length) (upRanks : v+1 ≤ upper.length) :
    (lower.length - (u+1)) + (upper.length - (v+1)) ≤
      outer.length - (u+v+1) := by
  have endpoint : label b ∈ upper := (upEnum _).2 ⟨b, refl b, bc, rfl⟩
  have shared {k} (lo : k ∈ lower) (up : k ∈ upper) : k = label b := by
    obtain ⟨x, _, xb, hx⟩ := (loEnum k).1 lo
    obtain ⟨y, by', _, hy⟩ := (upEnum k).1 up
    have xy := proper (trans xb by') (hx.trans hy.symm)
    subst y
    have heq := antisym xb by'
    subst x
    exact hx.symm
  let combined := lower ++ upper.erase (label b)
  have distinct : combined.Nodup := by
    apply List.pairwise_append.mpr
    refine ⟨loDistinct, upDistinct.erase _, ?_⟩
    intro k lo z hz heq
    subst z
    have atEndpoint := shared lo (List.mem_of_mem_erase hz)
    exact (List.Nodup.mem_erase_iff upDistinct |>.1 hz).1 atEndpoint
  have incl : ∀ k ∈ combined, k ∈ outer := by
    intro k hk
    apply (outEnum _).2
    rcases List.mem_append.mp hk with lo | up
    · obtain ⟨x, ax, xb, hx⟩ := (loEnum k).1 lo
      exact ⟨x, ax, trans xb bc, hx⟩
    · obtain ⟨x, bx, xc, hx⟩ := (upEnum k).1 (List.mem_of_mem_erase up)
      exact ⟨x, trans ab bx, xc, hx⟩
  have total := length_le_of_nodup_subset combined outer distinct incl
  simp only [combined, List.length_append, List.length_erase_of_mem endpoint] at total
  omega

private theorem ofFn_distinct {n : Nat} {K : Type} (f : Fin n → K)
    (inj : ∀ i j, f i = f j → i = j) : (List.ofFn f).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij same
  simp only [List.getElem_ofFn] at same
  have eq := congrArg Fin.val (inj _ _ same)
  exact (Nat.ne_of_lt hij) eq

/-- Patch the middle vertices of individual chains at nonconsecutive ranks.
    Every edge of the patched path occurs in a single-swap chain or the base. -/
theorem simultaneous_chain_steps {n : Nat} {V : Type} (step : V → V → Prop)
    (base : Fin n → V) (single : Fin n → Fin n → V) (active : Fin n → Bool)
    (baseStep : ∀ i j : Fin n, i.val+1 = j.val → step (base i) (base j))
    (singleStep : ∀ a i j : Fin n, active a = true → i.val+1 = j.val →
      step (single a i) (single a j))
    (offSlot : ∀ a j, j ≠ a → single a j = base j)
    (spaced : ∀ i j : Fin n, i.val+1 = j.val → active i = true → active j = false) :
    ∀ i j : Fin n, i.val+1 = j.val →
      step (if active i then single i i else base i)
           (if active j then single j j else base j) := by
  intro i j adj
  have ne : i ≠ j := by
    intro eq
    subst j
    omega
  cases hi : active i with
  | true =>
    have hj := spaced i j adj hi
    simpa [hi, hj, offSlot i j ne.symm] using singleStep i i j hi adj
  | false =>
    cases hj : active j with
    | true => simpa [hi, hj, offSlot j i ne] using singleStep j i j hj adj
    | false => simpa [hi, hj] using baseStep i j adj

/-- A base chain has n distinct codes. A single swap at each active slot
    changes its code only there. All chosen alternatives occur together on a
    chain with distinct codes. Count base codes and changed alternatives. -/
theorem independent_swap_count {n r c : Nat}
    (base : Fin n → Fin c) (slot : Fin r → Fin n)
    (single : Fin r → Fin n → Fin c) (joint : Fin n → Fin c)
    (baseInj : ∀ i j, base i = base j → i = j)
    (slotInj : ∀ i j, slot i = slot j → i = j)
    (singleInj : ∀ a i j, single a i = single a j → i = j)
    (offSlot : ∀ a j, j ≠ slot a → single a j = base j)
    (active : ∀ a, single a (slot a) ≠ base (slot a))
    (jointInj : ∀ i j, joint i = joint j → i = j)
    (appears : ∀ a, joint (slot a) = single a (slot a)) :
    n + r ≤ c := by
  let alt := fun a => single a (slot a)
  have altInj : ∀ a b, alt a = alt b → a = b := by
    intro a b h
    apply slotInj a b
    apply jointInj
    simpa only [appears] using h
  have apart : ∀ j a, base j ≠ alt a := by
    intro j a h
    by_cases hpos : j = slot a
    · subst j
      exact active a h.symm
    · apply hpos
      exact singleInj a j (slot a) ((offSlot a j hpos).trans h)
  let observed := List.ofFn base ++ List.ofFn alt
  have distinct : observed.Nodup := by
    apply List.pairwise_append.mpr
    refine ⟨ofFn_distinct base baseInj, ofFn_distinct alt altInj, ?_⟩
    intro x hx y hy
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hy
    exact apart j a
  let allCodes := List.ofFn (fun i : Fin c => i)
  have bound := length_le_of_nodup_subset observed allCodes distinct
    (fun a _ => List.mem_ofFn.mpr ⟨a, rfl⟩)
  simpa [observed, allCodes] using bound

/-- Index 0 is the first singleton. A later coordinate whose color is fresh
    when inserted and forbidden at and after insertion is never a seen color. -/
theorem greedy_overlap {K : Type} {k : Nat}
    (inserted : Fin (k+1) → K) (seenAt : Fin (k+1) → Option K)
    (first : seenAt 0 = some (inserted 0))
    (fresh : ∀ i t, t.val < i.val → seenAt t ≠ some (inserted i))
    (blocked : ∀ i t, i.val ≠ 0 → i.val ≤ t.val → seenAt t ≠ some (inserted i))
    (i : Fin (k+1)) :
    (∃ t, seenAt t = some (inserted i)) ↔ i.val = 0 := by
  constructor
  · rintro ⟨t, h⟩
    by_cases hn : i.val = 0
    · exact hn
    · exfalso
      by_cases prior : t.val < i.val
      · exact fresh i t prior h
      · exact blocked i t hn (by omega) h
  · intro h
    have eq : i = 0 := Fin.ext h
    subst i
    exact ⟨0, first⟩

/-- At termination k inserted coordinates and s seen colors exhaust r
    coordinates with one overlap. A completed chain omits at most q colors. -/
theorem greedy_terminal_bound {r k s q : Nat}
    (exhausted : r+1 = k+s) (seenSteps : s ≤ k) (missed : r ≤ s+q) :
    r ≤ 2*q+1 := by omega

end SwapCount
