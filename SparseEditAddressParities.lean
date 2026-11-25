import Std

namespace SparseEditAddressParities

/-- Parity of a selected set of bit positions, reading the specified addresses. -/
def scan (x : Nat → Bool) : List Nat → Bool
  | [] => false
  | a :: tail => x a ^^ scan x tail

theorem scan_xor (x y : Nat → Bool) (sites : List Nat) :
    scan (fun a => x a ^^ y a) sites = (scan x sites ^^ scan y sites) := by
  induction sites with
  | nil => rfl
  | cons a tail ih =>
    simp only [scan, ih]
    cases x a <;> cases y a <;> cases scan x tail <;> cases scan y tail <;> decide

theorem single_site (p : Nat) (f : Nat → Bool) (sites : List Nat) (unique : sites.Nodup) :
    scan (fun a => if a = p then f p else false) sites =
    (if p ∈ sites then f p else false) := by
  induction sites with
  | nil => simp [scan]
  | cons a tail ih =>
    obtain ⟨fresh, tailUnique⟩ := List.nodup_cons.mp unique
    simp only [scan, ih tailUnique, List.mem_cons]
    by_cases eq : a = p
    · subst a
      simp [fresh]
    · have rev : p ≠ a := Ne.symm eq
      simp [eq, rev]

def pick (t : Nat) (x : Nat → Bool) (sites : List Nat) : Bool :=
  scan (fun a => x a && a.testBit t) sites

def flip (x : Nat → Bool) (p q : Nat) : Nat → Bool :=
  fun a => (x a ^^ decide (a = p)) ^^ decide (a = q)

private theorem complement_selected (u w : Bool) : ((!u) && w) = ((u && w) ^^ w) := by
  cases u <;> cases w <;> rfl

theorem two_edit_formula (x : Nat → Bool) (p q t : Nat) (sites : List Nat)
    (h : sites.Nodup) (hp : p ∈ sites) (hq : q ∈ sites) :
    pick t (flip x p q) sites = ((pick t x sites ^^ p.testBit t) ^^ q.testBit t) := by
  let f := fun a : Nat => x a && a.testBit t
  let g := fun a : Nat => if a = p then p.testBit t else false
  let k := fun a : Nat => if a = q then q.testBit t else false
  have point : (fun a => flip x p q a && a.testBit t) = (fun a => (f a ^^ g a) ^^ k a) := by
    funext a
    by_cases ap : a = p <;> by_cases aq : a = q <;> simp_all [f, g, k, flip] <;> exact complement_selected _ _
  unfold pick
  rw [point, scan_xor, scan_xor]
  change ((scan f sites ^^ scan _ sites) ^^ scan _ sites) = _
  rw [show scan g sites = p.testBit t by exact (single_site p (fun a => a.testBit t) sites h).trans (if_pos hp),
      show scan k sites = q.testBit t by exact (single_site q (fun a => a.testBit t) sites h).trans (if_pos hq)]

theorem collision_mod (x : Nat → Bool) (p q b : Nat) (sites : List Nat)
    (h : sites.Nodup) (hp : p ∈ sites) (hq : q ∈ sites)
    (same : ∀ t < b, pick t (flip x p q) sites = pick t x sites) :
    p % 2^b = q % 2^b := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases lt : t < b
  · have identical := same t lt
    rw [two_edit_formula x p q t sites h hp hq] at identical
    have cancel (u v w : Bool) (eq : ((u ^^ v) ^^ w) = u) : v = w := by
      cases u <;> cases v <;> cases w <;> simp_all
    have bitEq := cancel _ _ _ identical
    simp [Nat.testBit_mod_two_pow, lt, bitEq]
  · simp [Nat.testBit_mod_two_pow, lt]

end SparseEditAddressParities
