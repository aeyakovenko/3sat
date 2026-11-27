import Std

namespace OrderedCertificates

/-- The cursor u is exclusive. A jump compares j with u−1 and recurs below j. -/
inductive Chain (f : Nat → α) (bad : Nat → Prop) : Nat → List α → Nat → Prop where
  | stop (u) : Chain f bad u [] u
  | jump {u j out labels} (lower : j < u) (same : f j = f (u-1)) (fails : bad j)
      (tail : Chain f bad j labels out) : Chain f bad u (f (u-1) :: labels) out

def Certificate (s n : Nat) (f : Nat → α) (bad : Nat → Prop) : Prop :=
  ∃ labels out, Chain f bad n labels out ∧ labels.length ≤ s+1 ∧
    (out = 0 ∨ (labels.length = s+1 ∧ labels.Nodup))

structure Suitable (s n μ : Nat) (f : Nat → α) where
  separates : ∀ {i j}, i < μ → μ ≤ j → j < n → f i ≠ f j
  pool : List α
  budget : pool.length ≤ s
  covers : ∀ {i}, μ ≤ i → i < n → f i ∈ pool

private theorem length_of_covered {xs ys : List α} (distinct : xs.Nodup)
    (inside : ∀ a ∈ xs, a ∈ ys) : xs.length ≤ ys.length := by
  classical
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    rcases List.nodup_cons.mp distinct with ⟨fresh, rest⟩
    have ha : a ∈ ys := inside a (by simp)
    have rem (b : α) (hb : b ∈ xs) : b ∈ ys.erase a := by
      have different : b ≠ a := fun h => fresh (h ▸ hb)
      exact (List.mem_erase_of_ne different).mpr (inside b (by simp [hb]))
    have le := ih rest rem
    have positive : 0 < ys.length := by cases ys <;> simp_all
    simp only [List.length_cons, List.length_erase_of_mem ha] at *
    omega

private theorem stays_above {s n μ : Nat} {f : Nat → α} {bad : Nat → Prop}
    (good : ¬bad μ) (suit : Suitable s n μ f) {u labels out}
    (chain : Chain f bad u labels out) (hi : μ < u) (bounded : u ≤ n) :
    μ < out ∧ ∀ a ∈ labels, a ∈ suit.pool := by
  induction chain with
  | stop u => exact ⟨hi, by simp⟩
  | @jump u j out labels lower same fails tail ih =>
    have keep : μ ≤ j := by
      by_cases h : j < μ
      · exact False.elim (suit.separates h (by omega) (by omega) same)
      · omega
    have ne : j ≠ μ := fun h => good (h ▸ fails)
    obtain ⟨endBound, cover⟩ := ih (by omega) (by omega)
    refine ⟨endBound, ?_⟩
    intro a member
    rcases List.mem_cons.mp member with eq | inTail
    · rw [eq]
      exact suit.covers (by omega) (by omega)
    · exact cover a inTail

theorem sound {s n μ : Nat} {f : Nat → α} {bad : Nat → Prop}
    (within : μ < n) (good : ¬bad μ) (suit : Suitable s n μ f) :
    ¬Certificate s n f bad := by
  rintro ⟨labels, out, chain, _, finish⟩
  obtain ⟨endBound, covered⟩ := stays_above good suit chain within (Nat.le_refl _)
  rcases finish with zero | ⟨long, distinct⟩
  · omega
  · have len := length_of_covered distinct covered
    have bound := suit.budget
    omega

private theorem earliest {P : Nat → Prop} {u} (existsHere : P u) :
    ∃ j, j ≤ u ∧ P j ∧ ∀ k < j, ¬P k := by
  induction u using Nat.strongRecOn with
  | ind u ih =>
    by_cases lower : ∃ k < u, P k
    · obtain ⟨k, cut, hk⟩ := lower
      obtain ⟨j, hj, property, first⟩ := ih k cut hk
      exact ⟨j, by omega, property, first⟩
    · exact ⟨u, Nat.le_refl _, existsHere, fun k hk p => lower ⟨k, hk, p⟩⟩

private theorem recorded_before {f : Nat → α} {bad : Nat → Prop} {u labels out}
    (chain : Chain f bad u labels out) {a : α} (mem : a ∈ labels) :
    ∃ i < u, f i = a := by
  induction chain with
  | stop => simp at mem
  | @jump u j out labels lower same fails tail ih =>
    rcases List.mem_cons.mp mem with eq | later
    · exact ⟨u-1, by omega, eq.symm⟩
    · obtain ⟨i, hi, hit⟩ := ih later
      exact ⟨i, by omega, hit⟩

private theorem build (f : Nat → α) {bad : Nat → Prop} (u fuel : Nat)
    (failure : ∀ k < u, bad k) :
    ∃ labels out, Chain f bad u labels out ∧ labels.Nodup ∧
      labels.length ≤ fuel ∧ (out = 0 ∨ labels.length = fuel) := by
  induction fuel generalizing u with
  | zero => exact ⟨[], u, .stop u, by simp, by simp, Or.inr rfl⟩
  | succ fuel ih =>
    by_cases empty : u = 0
    · subst u
      exact ⟨[], 0, .stop 0, by simp, by simp, Or.inl rfl⟩
    · obtain ⟨j, hj, same, first⟩ := earliest (P := fun i => f i = f (u-1)) (u := u-1) rfl
      have lower : j < u := by omega
      obtain ⟨labels, out, tail, distinct, bound, finish⟩ :=
        ih j (fun k hk => failure k (by omega))
      have fresh : f (u-1) ∉ labels := by
        intro member
        obtain ⟨k, hk, hit⟩ := recorded_before tail member
        exact first k hk hit
      refine ⟨_, out, .jump lower same (failure j lower) tail,
        List.nodup_cons.mpr ⟨fresh,distinct⟩, by simp; omega, ?_⟩
      rcases finish with done | full
      · exact Or.inl done
      · exact Or.inr (by simp [full])

theorem complete (f : Nat → α) {bad : Nat → Prop} (s n : Nat)
    (failure : ∀ k < n, bad k) : Certificate s n f bad := by
  obtain ⟨labels, out, chain, distinct, bound, done | full⟩ := build f n (s+1) failure
  · exact ⟨labels, out, chain, bound, Or.inl done⟩
  · exact ⟨labels, out, chain, bound, Or.inr ⟨full, distinct⟩⟩

/-- Coverage is required only on positives. Other menu entries may be arbitrary. -/
theorem menu {bad : Nat → Prop} {s n : Nat} (maps : ι → Nat → α)
    (coverage : (∃ w < n, ¬bad w) → ∃ i μ, μ < n ∧ ¬bad μ ∧ Nonempty (Suitable s n μ (maps i))) :
    (∃ w < n, ¬bad w) ↔ ∃ i, ¬Certificate s n (maps i) bad := by
  constructor
  · intro yes
    obtain ⟨i, μ, within, good, ⟨suit⟩⟩ := coverage yes
    exact ⟨i, sound within good suit⟩
  · rintro ⟨i, noCert⟩
    by_cases yes : ∃ w < n, ¬bad w
    · exact yes
    · have allBad (k : Nat) (hk : k < n) : bad k := by
        by_cases b : bad k
        · exact b
        · exact False.elim (yes ⟨k, hk, b⟩)
      exact False.elim (noCert (complete (maps i) s n allBad))

/-- Keep an outside left endpoint and an inside right endpoint. -/
def bisect (p : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, _, b => b
  | steps+1, a, b =>
    let m := (a+b)/2
    if p m then bisect p steps a m else bisect p steps m b

theorem bisect_spec (p : Nat → Bool) (steps a b : Nat) (left : p a = false)
    (right : p b = true) (ordered : a < b) (short : b-a ≤ 2^steps) :
    let j := bisect p steps a b
    a < j ∧ j ≤ b ∧ p j = true ∧ p (j-1) = false := by
  induction steps generalizing a b with
  | zero =>
    simp only [Nat.pow_zero] at short
    change a < b ∧ b ≤ b ∧ p b = true ∧ p (b-1) = false
    have eq : b-1 = a := by omega
    exact ⟨ordered, Nat.le_refl _, right, eq.symm ▸ left⟩
  | succ steps ih =>
    have scale : b-a ≤ 2^steps + 2^steps := by simpa [Nat.pow_succ,Nat.mul_two] using short
    let m := (a+b)/2
    have ma : a ≤ m := by dsimp [m]; omega
    have mb : m < b := by dsimp [m]; omega
    cases mid : p m with
    | true =>
      have ne : a ≠ m := by intro h; rw [h, mid] at left; contradiction
      obtain ⟨u,v,hit,prev⟩ := ih a m left mid (by omega) (by dsimp [m]; omega)
      have atMid : p ((a+b)/2) = true := mid
      simpa only [bisect, atMid, ↓reduceIte] using
        And.intro u (And.intro (Nat.le_trans v (Nat.le_of_lt mb)) (And.intro hit prev))
    | false =>
      obtain ⟨u,v,hit,prev⟩ := ih m b mid right mb (by dsimp [m]; omega)
      have atMid : p ((a+b)/2) = false := mid
      simpa only [bisect, atMid, Bool.false_eq_true, ↓reduceIte] using
        And.intro (Nat.lt_of_le_of_lt ma u) (And.intro v (And.intro hit prev))

/-- Any adjacent boundary can be used. A previous label may be reused at j. -/
inductive Listing (f : Nat → α) (s : Nat) : Nat → List α → List Nat → Prop where
  | empty (past) : Listing f s 0 past []
  | budget {u past} : s ≤ past.length → Listing f s u past []
  | more {u past j rest} (room : past.length < s) (lower : j < u)
      (hit : f j ∈ f (u-1) :: past)
      (boundary : j = 0 ∨ f (j-1) ∉ f (u-1) :: past)
      (tail : Listing f s j (f (u-1) :: past) rest) :
      Listing f s u past (j::rest)

private theorem listing_protects {f : Nat → α} {s n μ}
    (suit : Suitable s n μ f) {u past positions}
    (run : Listing f s u past positions) (hi : μ < u) (within : u ≤ n)
    (origin : ∀ l ∈ past, ∃ i, μ ≤ i ∧ i < n ∧ f i = l)
    (distinct : past.Nodup) (fresh : f (u-1) ∉ past) : μ ∈ positions := by
  induction run with
  | empty => omega
  | @budget u past spent =>
    have cover (a : α) (ha : a ∈ f (u-1) :: past) : a ∈ suit.pool := by
      rcases List.mem_cons.mp ha with eq | prev
      · rw [eq]; exact suit.covers (by omega) (by omega)
      · obtain ⟨w,above,below,eq⟩ := origin a prev
        rw [←eq]; exact suit.covers above below
    have bound := length_of_covered (List.nodup_cons.mpr ⟨fresh, distinct⟩) cover
    have budget := suit.budget
    simp only [List.length_cons] at bound
    omega
  | @more u past j rest room lower hit boundary tail ih =>
    have visited (a : α) (ha : a ∈ f (u-1) :: past) :
        ∃ i, μ ≤ i ∧ i < n ∧ f i = a := by
      rcases List.mem_cons.mp ha with rfl | prev
      · exact ⟨u-1,by omega,by omega,rfl⟩
      · exact origin a prev
    obtain ⟨k,above,below,same⟩ := visited (f j) hit
    have keep : μ ≤ j := by
      by_cases early : j < μ
      · exact False.elim (suit.separates early above below same.symm)
      · omega
    by_cases found : j = μ
    · simp [found]
    · have strict : μ < j := by omega
      have nextFresh : f (j-1) ∉ f (u-1) :: past := boundary.resolve_left (by omega)
      exact List.mem_cons_of_mem _ (ih strict (by omega) visited
        (List.nodup_cons.mpr ⟨fresh,distinct⟩) nextFresh)

theorem listing_covers {f : Nat → α} {s n μ} (suit : Suitable s n μ f)
    (within : μ < n) {positions} (run : Listing f s n [] positions) : μ ∈ positions :=
  listing_protects suit run within (Nat.le_refl _) (by simp) (by simp) (by simp)

end OrderedCertificates
