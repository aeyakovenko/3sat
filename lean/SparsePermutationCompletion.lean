import Std

namespace SparsePermutationCompletion

structure Permutation (α : Type) where
  apply : α → α
  undo : α → α
  undo_apply : ∀ x, undo (apply x) = x
  apply_undo : ∀ x, apply (undo x) = x

theorem Permutation.injective {α} (p : Permutation α) {x y} (eq : p.apply x = p.apply y) :
    x = y := by
  simpa [p.undo_apply] using congrArg p.undo eq

variable {α : Type} [DecidableEq α]

def swap (a b x : α) : α := if x = a then b else if x = b then a else x

@[simp] theorem swap_first (a b : α) : swap a b a = b := by simp [swap]
@[simp] theorem swap_second (a b : α) : swap a b b = a := by
  by_cases e : b = a <;> simp [swap, e]

@[simp] theorem swap_twice (a b x : α) : swap a b (swap a b x) = x := by
  by_cases ea : x = a
  · subst x; simp
  by_cases eb : x = b
  · subst x; simp
  simp [swap, ea, eb]

def swapOutputs (p : Permutation α) (a b : α) : Permutation α where
  apply x := swap a b (p.apply x)
  undo y := p.undo (swap a b y)
  undo_apply x := by simp [p.undo_apply]
  apply_undo y := by simp [p.apply_undo]

/-- Fix the tail first. Transposing the image of the head with its required
    image satisfies the head while leaving all distinct required tail images. -/
def complete (p : α → α) : List α → Permutation α
  | [] => ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  | x :: xs =>
    let tail := complete p xs
    swapOutputs tail (tail.apply x) (p x)

theorem agrees (p : α → α) (xs : List α) (distinct : xs.Nodup)
    (inj : ∀ a ∈ xs, ∀ b ∈ xs, p a = p b → a = b) :
    ∀ a ∈ xs, (complete p xs).apply a = p a := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, tailDistinct⟩ := List.nodup_cons.mp distinct
    have tail := ih tailDistinct (fun a ha b hb => inj a (by simp [ha]) b (by simp [hb]))
    intro a member
    rcases List.mem_cons.mp member with rfl | ha
    · simp [complete, swapOutputs]
    · have ne : a ≠ x := fun e => fresh (e ▸ ha)
      have diff : (complete p xs).apply a ≠ (complete p xs).apply x :=
        fun e => ne ((complete p xs).injective e)
      have other : (complete p xs).apply a ≠ p x := by
        rw [tail a ha]
        exact fun e => ne (inj a (by simp [ha]) x (by simp) e)
      simpa [complete, swapOutputs, swap, diff, other] using tail a ha

theorem fixed_outside (p : α → α) (xs : List α) (z : α)
    (out : z ∉ xs) (outImage : z ∉ xs.map p) : (complete p xs).apply z = z := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have nz : z ≠ x := fun e => out (by simp [e])
    have np : z ≠ p x := fun e => outImage (by simp [e])
    have old := ih (fun hz => out (by simp [hz])) (fun hz => outImage (by simp [hz]))
    have diff : (complete p xs).apply z ≠ (complete p xs).apply x :=
      fun e => nz ((complete p xs).injective e)
    have other : (complete p xs).apply z ≠ p x := by simpa [old] using np
    simpa [complete, swapOutputs, swap, diff, other] using old

theorem inverse_fixed_outside (p : α → α) (xs : List α) (z : α)
    (out : z ∉ xs) (outImage : z ∉ xs.map p) : (complete p xs).undo z = z := by
  calc
    (complete p xs).undo z = (complete p xs).undo ((complete p xs).apply z) :=
      congrArg _ (fixed_outside p xs z out outImage).symm
    _ = z := (complete p xs).undo_apply z

/-- An explicit cover of the support with length exactly twice the number of
    requested positions. It may contain duplicates when the two lists overlap. -/
theorem support_cover (p : α → α) (xs : List α) :
    ∃ cover : List α, cover.length = 2 * xs.length ∧
      ∀ z, (complete p xs).apply z ≠ z → z ∈ cover := by
  refine ⟨xs ++ xs.map p, by simp; omega, ?_⟩
  intro z moved
  by_cases original : z ∈ xs
  · simp [original]
  by_cases image : z ∈ xs.map p
  · simp [image]
  exact False.elim (moved (fixed_outside p xs z original image))

def swapInputs (p : Permutation α) (a b : α) : Permutation α where
  apply x := p.apply (swap a b x)
  undo y := swap a b (p.undo y)
  undo_apply x := by simp [p.undo_apply]
  apply_undo y := by simp [p.apply_undo]

/-- Swapping two unrequested addresses preserves every requested answer and
    really changes the permutation. All other addresses retain their images. -/
theorem free_transposition (q : Permutation α) (xs : List α) {a b : α}
    (aFree : a ∉ xs) (bFree : b ∉ xs) (different : a ≠ b) :
    (∀ x ∈ xs, (swapInputs q a b).apply x = q.apply x) ∧
    (swapInputs q a b).apply a = q.apply b ∧ (swapInputs q a b).apply b = q.apply a ∧
    (swapInputs q a b).apply a ≠ q.apply a ∧
    (∀ x, x ≠ a → x ≠ b → (swapInputs q a b).apply x = q.apply x) := by
  have outside (x : α) (ha : x ≠ a) (hb : x ≠ b) :
      (swapInputs q a b).apply x = q.apply x := by simp [swapInputs, swap, ha, hb]
  refine ⟨fun x hx => outside x (fun eq => aFree (eq ▸ hx)) (fun eq => bFree (eq ▸ hx)),
    by simp [swapInputs], by simp [swapInputs], ?_, outside⟩
  simpa [swapInputs] using (show q.apply b ≠ q.apply a from fun eq => different (q.injective eq).symm)

private theorem reserve_pair (xs extra : List α) (different : extra.Nodup)
    (free : ∀ x ∈ extra, x ∉ xs) (two : ∃ a b, a ∉ xs ∧ b ∉ xs ∧ a ≠ b) :
    ∃ a b, ∃ pool : List α, a ∉ xs ∧ b ∉ xs ∧ a ≠ b ∧ a ∈ pool ∧ b ∈ pool ∧
      (∀ x ∈ extra, x ∈ pool) ∧ pool.length ≤ max extra.length 2 := by
  obtain ⟨u, v, hu, hv, uv⟩ := two
  cases extra with
  | nil => exact ⟨u, v, [u,v], hu, hv, uv, by simp, by simp, by simp, by simp⟩
  | cons a rest =>
    have ha := free a (by simp)
    cases rest with
    | nil =>
      have other : ∃ b, b ∉ xs ∧ a ≠ b := by
        by_cases au : a = u
        · exact ⟨v, hv, au ▸ uv⟩
        · exact ⟨u, hu, au⟩
      obtain ⟨b, hb, ab⟩ := other
      exact ⟨a, b, [a,b], ha, hb, ab, by simp, by simp, by simp, Nat.le_max_right _ _⟩
    | cons b rest =>
      have ab : a ≠ b := fun e => (List.nodup_cons.mp different).1 (by simp [e])
      exact ⟨a, b, a::b::rest, ha, free b (by simp), ab, by simp, by simp,
        fun _ h => h, Nat.le_max_left _ _⟩

/-- With at least two unpinned positions, the completion and a transposed
    alternative both have support in a single list of length at most max(2s,s+2).
    We prefer unused positions already present among the requested images. -/
theorem two_sparse_completions (p : α → α) (xs : List α) (distinct : xs.Nodup)
    (inj : ∀ a ∈ xs, ∀ b ∈ xs, p a = p b → a = b)
    (two : ∃ a b, a ∉ xs ∧ b ∉ xs ∧ a ≠ b) :
    ∃ a b, ∃ cover : List α, a ∉ xs ∧ b ∉ xs ∧ a ≠ b ∧
      cover.length ≤ max (2 * xs.length) (xs.length + 2) ∧
      ∀ z, z ∉ cover → (complete p xs).apply z = z ∧
        (swapInputs (complete p xs) a b).apply z = z := by
  let extra := (xs.map p).filter (fun v => decide (v ∉ xs))
  have distinctImage : (xs.map p).Nodup := List.pairwise_map.mpr
    (distinct.imp_of_mem (fun ha hb ne eq => ne (inj _ ha _ hb eq)))
  have fresh (y : α) (hy : y ∈ extra) : y ∉ xs := by
    exact of_decide_eq_true (List.mem_filter.mp hy).2
  obtain ⟨a, b, pool, ha, hb, ab, ap, bp, covers, small⟩ :=
    reserve_pair xs extra (distinctImage.filter _) fresh two
  have extraSize : extra.length ≤ xs.length := by simpa [extra] using
    (List.length_filter_le (fun v => decide (v ∉ xs)) (xs.map p))
  refine ⟨a, b, xs ++ pool, ha, hb, ab, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro z outside
    have notX : z ∉ xs := fun h => outside (List.mem_append.mpr (Or.inl h))
    have notPool : z ∉ pool := fun h => outside (List.mem_append.mpr (Or.inr h))
    have notY : z ∉ xs.map p := fun h => notPool (covers z
      (List.mem_filter.mpr ⟨h, decide_eq_true notX⟩))
    have same := fixed_outside p xs z notX notY
    have za : z ≠ a := fun e => notPool (e ▸ ap)
    have zb : z ≠ b := fun e => notPool (e ▸ bp)
    exact ⟨same, by simpa [swapInputs, swap, za, zb] using same⟩

def inversions : List Nat → Nat
  | [] => 0
  | x :: xs => (xs.filter (· < x)).length + inversions xs

private theorem adjacent_flip (pre : List Nat) {a b : Nat} (different : a ≠ b) (rest : List Nat) :
    (inversions (pre ++ a :: b :: rest) + inversions (pre ++ b :: a :: rest)) % 2 = 1 := by
  induction pre with
  | nil =>
    by_cases ab : a < b
    · have ba : ¬ b < a := by omega
      simp [inversions, List.filter_cons, ab, ba]
      omega
    · have ba : b < a := by omega
      simp [inversions, List.filter_cons, ab, ba]
      omega
  | cons x pre ih =>
    have perm := List.Perm.append_left pre (List.Perm.swap b a rest)
    have counts := (List.Perm.filter (fun y => decide (y < x)) perm).length_eq
    simp only [List.cons_append, inversions]
    omega

/-- In an ordered finite permutation table all entries are distinct. Swapping
    two entries, at any distance, reverses the parity of its inversion count. -/
theorem transposition_flips_inversions (pre middle post : List Nat) (a b : Nat)
    (ab : a ≠ b) (aFresh : a ∉ middle) (bFresh : b ∉ middle) :
    (inversions (pre ++ a :: (middle ++ b :: post)) +
     inversions (pre ++ b :: (middle ++ a :: post))) % 2 = 1 := by
  induction middle generalizing pre with
  | nil => exact adjacent_flip pre ab post
  | cons z zs ih =>
    have az : a ≠ z := fun e => aFresh (by simp [e])
    have zb : z ≠ b := fun e => bFresh (by simp [e])
    have left := adjacent_flip pre az (zs ++ b :: post)
    have center := ih (pre ++ [z]) (fun h => aFresh (by simp [h])) (fun h => bFresh (by simp [h]))
    have right := adjacent_flip pre zb (zs ++ a :: post)
    simp only [List.append_assoc, List.singleton_append] at center
    simp only [List.cons_append]
    omega

/-- Read a permutation table in a fixed order and encode values by distinct
    natural ranks. Swapping the inputs at its two distinguished positions flips
    the actual inversion parity of that same ordered table. -/
theorem swapped_table_parity (q : Permutation α) (rank : α → Nat)
    (rankInj : ∀ x y, rank x = rank y → x = y)
    (pre middle post : List α) (a b : α) (ab : a ≠ b)
    (ha : a ∉ pre ++ middle ++ post) (hb : b ∉ pre ++ middle ++ post) :
    let indices := pre ++ a :: (middle ++ b :: post)
    (inversions (indices.map (fun x => rank (q.apply x))) +
     inversions (indices.map (fun x => rank ((swapInputs q a b).apply x)))) % 2 = 1 := by
  let f := fun x => rank (q.apply x)
  let g := fun x => rank ((swapInputs q a b).apply x)
  have inj {x y} (eq : f x = f y) : x = y := q.injective (rankInj _ _ eq)
  have unchanged (part : List α) (sub : ∀ x ∈ part, x ∈ pre ++ middle ++ post) :
      part.map g = part.map f := by
    apply List.map_congr_left
    intro x hx
    have xa : x ≠ a := fun eq => ha (eq ▸ sub x hx)
    have xb : x ≠ b := fun eq => hb (eq ▸ sub x hx)
    simp [g, f, swapInputs, swap, xa, xb]
  have first := unchanged pre (fun x hx => by simp [hx])
  have internal := unchanged middle (fun x hx => by simp [hx])
  have last := unchanged post (fun x hx => by simp [hx])
  have newA : g a = f b := by simp [g, f, swapInputs]
  have newB : g b = f a := by simp [g, f, swapInputs]
  have fresh (x : α) (h : x ∉ pre ++ middle ++ post) : f x ∉ middle.map f := by
    rintro member
    obtain ⟨z, hz, same⟩ := List.mem_map.mp member
    have eq := inj same
    subst z
    exact h (by simp [hz])
  change (inversions ((pre ++ a :: (middle ++ b :: post)).map f) +
    inversions ((pre ++ a :: (middle ++ b :: post)).map g)) % 2 = 1
  simp only [List.map_append, List.map_cons, first, internal, last, newA, newB]
  exact transposition_flips_inversions _ _ _ _ _ (fun e => ab (inj e)) (fresh a ha) (fresh b hb)

end SparsePermutationCompletion
