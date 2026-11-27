import Std

namespace DyadicCspProjection

/-- Binary coordinate vectors with a distinguished first coordinate. -/
def Bits : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Bits n

abbrev Family (n : Nat) := Bits n → Bool

inductive Coords : Nat → Nat → Type where
  | empty : Coords 0 0
  | skip : Coords n k → Coords (n+1) k
  | take : Coords n k → Coords (n+1) (k+1)

def proj : Coords n k → Bits n → Bits k
  | .empty, _ => ()
  | .skip m, x => proj m x.2
  | .take m, x => (x.1, proj m x.2)

def left (F : Family (n+1)) : Family n := fun x => F (false,x)
def right (F : Family (n+1)) : Family n := fun x => F (true,x)
def join (F G : Family n) : Family n := fun x => F x || G x
def meet (F G : Family n) : Family n := fun x => F x && G x

def shatters : Coords n k → Family n → Prop
  | .empty, F => F () = true
  | .skip m, F => shatters m (join (left F) (right F))
  | .take m, F => shatters m (left F) ∧ shatters m (right F)

theorem shatters_iff_all_patterns (m : Coords n k) (F : Family n) :
    shatters m F ↔ ∀ b : Bits k, ∃ x : Bits n, F x = true ∧ proj m x = b := by
  induction m with
  | empty => exact ⟨fun h _ => ⟨(), h, rfl⟩, fun h => (h ()).choose_spec.1⟩
  | skip m ih =>
    rw [shatters, ih]
    constructor
    · intro h b
      obtain ⟨x,hx,hp⟩ := h b
      have h' : left F x = true ∨ right F x = true := by simpa [join] using hx
      rcases h' with h0 | h1
      · exact ⟨(false,x), h0, hp⟩
      · exact ⟨(true,x), h1, hp⟩
    · intro h b
      obtain ⟨⟨a,x⟩,hx,hp⟩ := h b
      refine ⟨x, ?_, hp⟩
      cases a <;> simp_all [join, left, right]
  | take m ih =>
    rw [shatters, ih, ih]
    constructor
    · rintro ⟨h0,h1⟩ ⟨a,b⟩
      cases a with
      | false =>
        obtain ⟨x,hx,hp⟩ := h0 b
        exact ⟨(false,x), hx, by simp [proj, hp]⟩
      | true =>
        obtain ⟨x,hx,hp⟩ := h1 b
        exact ⟨(true,x), hx, by simp [proj, hp]⟩
    · intro h
      constructor
      · intro b
        obtain ⟨⟨a,x⟩,hx,hp⟩ := h (false,b)
        obtain ⟨rfl, hp'⟩ := Prod.mk.inj hp
        exact ⟨x,hx,hp'⟩
      · intro b
        obtain ⟨⟨a,x⟩,hx,hp⟩ := h (true,b)
        obtain ⟨rfl, hp'⟩ := Prod.mk.inj hp
        exact ⟨x,hx,hp'⟩

theorem shatters_mono (m : Coords n k) (F G : Family n)
    (h : ∀ x, F x = true → G x = true) : shatters m F → shatters m G := by
  rw [shatters_iff_all_patterns, shatters_iff_all_patterns]
  intro all b
  obtain ⟨x, hx, hp⟩ := all b
  exact ⟨x,h x hx,hp⟩

def count : (n : Nat) → Family n → Nat
  | 0, F => if F () then 1 else 0
  | n+1, F => count n (left F) + count n (right F)

theorem union_inter_count (n : Nat) (F G : Family n) :
    count n (join F G) + count n (meet F G) = count n F + count n G := by
  induction n with
  | zero => cases h : F () <;> cases h' : G () <;> simp [count, join, meet, h, h']
  | succ n ih =>
    have a := ih (left F) (left G)
    have b := ih (right F) (right G)
    change (count n (join (left F) (left G)) + count n (join (right F) (right G))) +
      (count n (meet (left F) (left G)) + count n (meet (right F) (right G))) = _
    simp only [count]
    omega

/-- Number of subsets of n coordinates with cardinality strictly smaller than k,
given by Pascal recursion. -/
def cap : Nat → Nat → Nat
  | 0, 0 => 0
  | 0, _+1 => 1
  | _+1, 0 => 0
  | n+1, k+1 => cap n (k+1) + cap n k

/-- The bound needed on each union of the dyadic coordinate intervals. -/
theorem forbidden_pattern_bound (n k : Nat) (F : Family n)
    (noFull : ∀ m : Coords n k, ¬ shatters m F) : count n F ≤ cap n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero =>
      have h := noFull .empty
      change ¬ F () = true at h
      simp [count, cap, h]
    | succ k =>
      cases h : F () <;> simp [count, cap, h]
  | succ n ih =>
    have hJoin : ∀ m : Coords n k, ¬ shatters m (join (left F) (right F)) :=
      fun m => noFull (.skip m)
    cases k with
    | zero =>
      have h0 := ih 0 (left F) (fun m h => hJoin m
        (shatters_mono m _ _ (fun x hx => by simp [join, hx]) h))
      have h1 := ih 0 (right F) (fun m h => hJoin m
        (shatters_mono m _ _ (fun x hx => by simp [join, hx]) h))
      have z : cap n 0 = 0 := by cases n <;> rfl
      simp only [count, cap]
      omega
    | succ k =>
      have hMeet : ∀ m : Coords n k, ¬ shatters m (meet (left F) (right F)) := by
        intro m both
        apply noFull (.take m)
        constructor
        · exact shatters_mono m _ _ (fun x hx => (Bool.and_eq_true_iff.mp hx).1) both
        · exact shatters_mono m _ _ (fun x hx => (Bool.and_eq_true_iff.mp hx).2) both
      have hj := ih (k+1) _ hJoin
      have hm := ih k _ hMeet
      have counts := union_inter_count n (left F) (right F)
      simp only [count, cap]
      omega

theorem count_if_every_tuple_omits_a_pattern (n k : Nat) (F : Family n)
    (forbidden : ∀ m : Coords n k, ∃ b : Bits k, ∀ x, F x = true → proj m x ≠ b) :
    count n F ≤ cap n k := by
  apply forbidden_pattern_bound
  intro m all
  obtain ⟨b, impossiblePattern⟩ := forbidden m
  obtain ⟨x, hx, hp⟩ := (shatters_iff_all_patterns m F).mp all b
  exact impossiblePattern x hx hp

#print axioms shatters_iff_all_patterns
#print axioms forbidden_pattern_bound


/-- The Boolean family of all shattered coordinate masks. Skipping projects away
the first coordinate, while keeping it requires every tail pattern on both sides. -/
def shatteredMasks : (n : Nat) → Family n → Family n
  | 0, F, _ => F ()
  | n+1, F, (false,m) => shatteredMasks n (join (left F) (right F)) m
  | n+1, F, (true,m) =>
    shatteredMasks n (left F) m && shatteredMasks n (right F) m

def asMask : Coords n k → Bits n
  | .empty => ()
  | .skip m => (false, asMask m)
  | .take m => (true, asMask m)

theorem mask_iff_shatters (m : Coords n k) (F : Family n) :
    shatteredMasks n F (asMask m) = true ↔ shatters m F := by
  induction m with
  | empty => rfl
  | skip m ih => exact ih _
  | take m ih => simp only [shatteredMasks, asMask, Bool.and_eq_true, ih, shatters]

theorem all_masks_represented (n : Nat) (b : Bits n) :
    ∃ k, ∃ m : Coords n k, asMask m = b := by
  induction n with
  | zero => exact ⟨0, .empty, rfl⟩
  | succ n ih =>
    obtain ⟨side, rest⟩ := b
    obtain ⟨k,m,hm⟩ := ih rest
    cases side with
    | false => exact ⟨k, .skip m, by simp [asMask,hm]⟩
    | true => exact ⟨k+1, .take m, by simp [asMask,hm]⟩

theorem count_mono (n : Nat) (F G : Family n)
    (sub : ∀ x, F x = true → G x = true) : count n F ≤ count n G := by
  induction n with
  | zero =>
    have h := sub ()
    cases hF : F () <;> cases hG : G () <;> simp_all [count]
  | succ n ih =>
    apply Nat.add_le_add
    · exact ih (left F) (left G) (fun x => sub (false,x))
    · exact ih (right F) (right G) (fun x => sub (true,x))

/-- The cardinality of any family is bounded by its number of shattered subsets,
including when the missing supports form a nonuniform independence system. -/
theorem strong_sauer (n : Nat) (F : Family n) :
    count n F ≤ count n (shatteredMasks n F) := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    let l := left F
    let r := right F
    have cross : count n (shatteredMasks n (meet l r)) ≤
        count n (meet (shatteredMasks n l) (shatteredMasks n r)) := by
      apply count_mono
      intro b hs
      obtain ⟨k,m,hm⟩ := all_masks_represented n b
      subst b
      have h := (mask_iff_shatters m _).mp hs
      apply Bool.and_eq_true_iff.mpr
      constructor
      · apply (mask_iff_shatters m _).mpr
        exact shatters_mono m _ _ (fun x hx => (Bool.and_eq_true_iff.mp hx).1) h
      · apply (mask_iff_shatters m _).mpr
        exact shatters_mono m _ _ (fun x hx => (Bool.and_eq_true_iff.mp hx).2) h
    have hj := ih (join l r)
    have hm := ih (meet l r)
    have total := union_inter_count n l r
    change count n l + count n r ≤ count n (shatteredMasks n (join l r)) +
      count n (meet (shatteredMasks n l) (shatteredMasks n r))
    omega

/-- If the old pair can trigger a clause forbidding one extension bit, the family
of rows allowing both extensions cannot shatter that pair. -/
theorem ambiguous_rows_omit_pair (m : Coords n 2) (target : Bits 2) (sign : Bool)
    (ok : Bits n → Bool → Bool)
    (forbid : ∀ x, proj m x = target → ok x sign = false) :
    ¬shatters m (fun x => ok x false && ok x true) := by
  intro sh
  obtain ⟨x, hx, hp⟩ := (shatters_iff_all_patterns m _).mp sh target
  have h := forbid x hp
  have both := Bool.and_eq_true_iff.mp hx
  cases sign <;> simp_all

#print axioms strong_sauer
#print axioms ambiguous_rows_omit_pair

end DyadicCspProjection
