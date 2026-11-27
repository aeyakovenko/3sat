import Std

namespace BinaryHistoryCatalogBound

private def grid (f : A → B → C) (as : List A) (bs : List B) : List C :=
  as.flatMap fun a => bs.map (f a)

private theorem grid_size (f : A → B → C) (as : List A) (bs : List B) :
    (grid f as bs).length = as.length * bs.length := by
  induction as with
  | nil => simp [grid]
  | cons a as ih =>
    simp only [grid, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, Nat.succ_mul] at *
    omega

private theorem grid_distinct (f : A → B → C) (as : List A) (bs : List B)
    (ha : as.Nodup) (hb : bs.Nodup)
    (injective : ∀ a b a' b', f a b = f a' b' → a = a' ∧ b = b') :
    (grid f as bs).Nodup := by
  apply List.pairwise_flatMap.2
  constructor
  · intro a _
    exact List.pairwise_map.2 (hb.imp (fun ne eq => ne (injective _ _ _ _ eq).2))
  · apply ha.imp
    intro a a' ne u hu v hv eq
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 hu
    obtain ⟨b', _, rfl⟩ := List.mem_map.1 hv
    exact ne (injective _ _ _ _ eq).1

private def words (alphabet : List A) : Nat → List (List A)
  | 0 => [[]]
  | n+1 => grid List.cons alphabet (words alphabet n)

private theorem word_size (alphabet : List A) (n : Nat) :
    (words alphabet n).length = alphabet.length^n := by
  induction n with
  | zero => simp [words]
  | succ n ih => simp [words, grid_size, ih, Nat.pow_succ, Nat.mul_comm]

private theorem word_distinct (alphabet : List A) (h : alphabet.Nodup) (n : Nat) :
    (words alphabet n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih => exact grid_distinct List.cons _ _ h ih (fun _ _ _ _ eq => List.cons.inj eq)

private theorem mem_words (alphabet : List A) (n : Nat) (xs : List A) :
    xs ∈ words alphabet n ↔ xs.length = n ∧ ∀ x ∈ xs, x ∈ alphabet := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [words]
  | succ n ih =>
    cases xs with
    | nil => simp [words, grid]
    | cons x xs => simp [words, grid, ih, and_left_comm]

private def rectangle (R : List A) (P : List B) (d h : Nat) :=
  grid Prod.mk (words R d) (words P h)

private theorem rectangle_size (R : List A) (P : List B) (d h : Nat) :
    (rectangle R P d h).length = R.length^d * P.length^h := by
  simp [rectangle, grid_size, word_size]

private theorem included_size (xs ys : List A) [DecidableEq A] (hx : xs.Nodup)
    (inside : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp hx
    have mem := inside x (by simp)
    have pos := List.length_pos_of_mem mem
    have rest := ih (ys.erase x) tail (by
      intro a ha
      have ne : a ≠ x := fun eq => fresh (eq ▸ ha)
      exact (List.mem_erase_of_ne ne).2 (inside a (by simp [ha])))
    rw [List.length_erase_of_mem mem] at rest
    simp
    omega

/-- Every tuple of root challenges and position challenges must be explained
    by one common catalog member. Each side is sampled with replacement.
    Different candidates' rectangles may overlap arbitrarily. -/
theorem joint_rectangle_sum (rootDomain : List A) (positionDomain : List B)
    (candidates : List C) (roots : C → List A) (positions : C → List B) (d h : Nat)
    (rd : rootDomain.Nodup) (pd : positionDomain.Nodup)
    (cover : ∀ (u : List A) (v : List B), u.length = d → v.length = h →
      (∀ x ∈ u, x ∈ rootDomain) → (∀ y ∈ v, y ∈ positionDomain) →
      ∃ c ∈ candidates, (∀ x ∈ u, x ∈ roots c) ∧ (∀ y ∈ v, y ∈ positions c)) :
    rootDomain.length^d * positionDomain.length^h ≤
      (candidates.map (fun c => (roots c).length^d * (positions c).length^h)).sum := by
  classical
  let pool := candidates.flatMap fun c => rectangle (roots c) (positions c) d h
  have full : (rectangle rootDomain positionDomain d h).Nodup :=
    grid_distinct Prod.mk _ _ (word_distinct _ rd d) (word_distinct _ pd h)
      (fun _ _ _ _ eq => Prod.mk.inj eq)
  have bound := included_size (rectangle rootDomain positionDomain d h) pool full (by
    rintro ⟨u,v⟩ mem
    have mem' : u ∈ words rootDomain d ∧ v ∈ words positionDomain h := by
      simpa [rectangle, grid] using mem
    obtain ⟨du, ru⟩ := (mem_words ..).1 mem'.1
    obtain ⟨hv, pv⟩ := (mem_words ..).1 mem'.2
    obtain ⟨c, hc, ur, vp⟩ := cover u v du hv ru pv
    apply List.mem_flatMap.2
    refine ⟨c, hc, ?_⟩
    simpa [rectangle, grid] using
      And.intro ((mem_words (roots c) d u).2 ⟨du, ur⟩)
        ((mem_words (positions c) h v).2 ⟨hv, vp⟩))
  simpa [pool, List.length_flatMap, rectangle_size] using bound

/-- The uniform bound q^d T^h ≤ number_of_candidates · D^d · Z^h for
    root sets of size at most D and position sets of size at most Z. -/
theorem joint_catalog_bound (rootDomain : List A) (positionDomain : List B)
    (candidates : List C) (roots : C → List A) (positions : C → List B) (d h D Z : Nat)
    (rd : rootDomain.Nodup) (pd : positionDomain.Nodup)
    (sizes : ∀ c ∈ candidates, (roots c).length ≤ D ∧ (positions c).length ≤ Z)
    (cover : ∀ (u : List A) (v : List B), u.length = d → v.length = h →
      (∀ x ∈ u, x ∈ rootDomain) → (∀ y ∈ v, y ∈ positionDomain) →
      ∃ c ∈ candidates, (∀ x ∈ u, x ∈ roots c) ∧ (∀ y ∈ v, y ∈ positions c)) :
    rootDomain.length^d * positionDomain.length^h ≤ candidates.length * D^d * Z^h := by
  apply Nat.le_trans (joint_rectangle_sum rootDomain positionDomain candidates roots positions d h rd pd cover)
  clear cover
  induction candidates with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨dr, zp⟩ := sizes c (by simp)
    have one := Nat.mul_le_mul (Nat.pow_le_pow_left dr d) (Nat.pow_le_pow_left zp h)
    have rest := ih (fun z hz => sizes z (List.mem_cons_of_mem _ hz))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, Nat.add_mul]
    omega

end BinaryHistoryCatalogBound
