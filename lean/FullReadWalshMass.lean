import Std

namespace FullReadWalshMass

abbrev Word := List Bool
abbrev Trace := List (Option Bool)

def sign : Word → Int
  | [] => 1
  | false :: xs => sign xs
  | true :: xs => -sign xs

def mass : List Word → Int
  | [] => 0
  | x :: xs => sign x + mass xs

def fill : Trace → List Word
  | [] => [[]]
  | some b :: xs => (fill xs).map (b :: ·)
  | none :: xs => (fill xs).map (false :: ·) ++ (fill xs).map (true :: ·)

def filled : Trace → Bool
  | [] => true
  | some _ :: xs => filled xs
  | none :: _ => false

private theorem mass_append (xs ys : List Word) :
    mass (xs ++ ys) = mass xs + mass ys := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih => simp [mass, ih, Int.add_assoc]

private theorem mass_prefix (b : Bool) (xs : List Word) :
    mass (xs.map (b :: ·)) = if b then -mass xs else mass xs := by
  induction xs with
  | nil => cases b <;> simp [mass]
  | cons x xs ih => cases b <;> simp [mass, sign] at * <;> omega

theorem unread_cancels (p : Trace) (miss : filled p = false) : mass (fill p) = 0 := by
  induction p with
  | nil => simp [filled] at miss
  | cons a p ih =>
    cases a with
    | none => simp [fill, mass_append, mass_prefix]; omega
    | some b =>
      have h := ih miss
      cases b <;> simp [fill, mass_prefix, h]

theorem exposed_one (p : Trace) (hit : filled p = true) :
    (fill p).length = 1 ∧ (mass (fill p) = -1 ∨ mass (fill p) = 1) := by
  induction p with
  | nil => simp [fill, mass, sign]
  | cons a p ih =>
    cases a with
    | none => simp [filled] at hit
    | some b =>
      obtain ⟨len, h⟩ := ih hit
      cases b <;> rcases h with h | h <;> simp [fill, mass_prefix, len, h]

private theorem mass_perm {xs ys : List Word} (h : xs.Perm ys) :
    mass xs = mass ys := by
  induction h with
  | nil => rfl
  | cons x h ih => simp [mass, ih]
  | swap x y l => simp [mass]; omega
  | trans _ _ ih jh => exact ih.trans jh

private theorem leaf_bounds (p : Trace) :
    -(if filled p then (1 : Int) else 0) ≤ mass (fill p) ∧
    mass (fill p) ≤ (if filled p then (1 : Int) else 0) := by
  cases h : filled p with
  | false => simp [unread_cancels p h]
  | true => rcases (exposed_one p h).2 with hp | hp <;> simp [hp]

/-- The partitions for accepting and rejecting inputs may be used independently.
    A permutation of the flattened leaf lists enforces exact multiplicities. -/
theorem full_read_bound (leaves : List Trace) (inputs : List Word)
    (partition : inputs.Perm (leaves.flatMap fill)) :
    -(leaves.countP filled : Int) ≤ mass inputs ∧ mass inputs ≤ (leaves.countP filled : Int) := by
  rw [mass_perm partition]
  clear partition inputs
  induction leaves with
  | nil => simp [mass]
  | cons p ps ih =>
    rw [List.flatMap_cons, mass_append, List.countP_cons]
    have one := leaf_bounds p
    cases h : filled p <;> simp [h] at * <;> omega

end FullReadWalshMass
