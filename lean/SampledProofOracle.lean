import Std

namespace SampledProofOracle

/-- A deterministic adaptive query procedure, for one fixed tuple of verifier coins. -/
inductive Tree (Addr : Type) where
  | done (accept : Bool)
  | query (address : Addr) (onFalse onTrue : Tree Addr)

variable {Addr : Type}
abbrev Tape (Addr : Type) := Addr → Bool
abbrev Pins (Addr : Type) := List (Addr × Bool)

def height : Tree Addr → Nat
  | .done _ => 0
  | .query _ left right => (max (height left) (height right)) + 1

def eval (t : Tape Addr) : Tree Addr → Bool
  | .done b => b
  | .query a left right => if t a then eval t right else eval t left

def matchesPins (pins : Pins Addr) (t : Tape Addr) : Bool :=
  pins.all fun p => t p.1 == p.2

def hits (pool : List (Tape Addr)) (event : Tape Addr → Bool) : Nat :=
  (pool.map (fun t => (event t).toNat)).sum

def accepted (pool : List (Tape Addr)) (pins : Pins Addr) (tree : Tree Addr) : Nat :=
  hits pool fun t => matchesPins pins t && eval t tree

@[simp] private theorem pin_cons (a : Addr) (v : Bool) (pins : Pins Addr) (t : Tape Addr) :
    matchesPins ((a,v)::pins) t = ((t a == v) && matchesPins pins t) := rfl

private theorem accepted_cons (t : Tape Addr) (ts : List (Tape Addr)) (pins) (tree) :
    accepted (t::ts) pins tree = (matchesPins pins t && eval t tree).toNat + accepted ts pins tree := rfl

@[simp] private theorem hits_false (pool : List (Tape Addr)) : hits pool (fun _ => false) = 0 := by
  induction pool with
  | nil => rfl
  | cons t ts ih => simpa [hits] using ih

/-- The two subtrees use disjoint events because the actual same tape supplies
    the next answer. Pre-existing pins are retained on both branches. -/
private theorem split (pool : List (Tape Addr)) (pins : Pins Addr) (a : Addr) (l r : Tree Addr) :
    accepted pool pins (.query a l r) =
      accepted pool ((a,false)::pins) l + accepted pool ((a,true)::pins) r := by
  induction pool with
  | nil => simp [accepted, hits]
  | cons t ts ih =>
    have one : (matchesPins pins t && eval t (.query a l r)).toNat =
        (matchesPins ((a,false)::pins) t && eval t l).toNat +
        (matchesPins ((a,true)::pins) t && eval t r).toNat := by
      cases ha : t a <;> cases hp : matchesPins pins t <;>
        cases hl : eval t l <;> cases hr : eval t r <;> simp [eval, ha, hp, hl, hr]
    rw [accepted_cons, accepted_cons, accepted_cons, one, ih]
    omega

/-- Equality of frequencies on all cubes of the remaining depth implies
    equality for a fully adaptive tree. The integer scales allow pools of
    different cardinalities. Repeated queries require no independence. -/
theorem adaptive_transfer (tree : Tree Addr) (pins : Pins Addr) (p q : List (Tape Addr))
    (a b : Nat) (same : ∀ extra : Pins Addr, extra.length ≤ height tree →
      a * hits p (matchesPins (extra ++ pins)) = b * hits q (matchesPins (extra ++ pins))) :
    a * accepted p pins tree = b * accepted q pins tree := by
  induction tree generalizing pins with
  | done verdict =>
    cases verdict
    · simp [accepted, eval]
    · simpa [accepted, eval] using same [] (by simp [height])
  | query addr left right il ir =>
    rw [split, split, Nat.mul_add, Nat.mul_add]
    congr 1
    · apply il
      intro extra bound
      have h := same (extra ++ [(addr,false)]) (by
        simp [height]; exact Nat.le_trans bound (Nat.le_max_left _ _))
      simpa using h
    · apply ir
      intro extra bound
      have h := same (extra ++ [(addr,true)]) (by
        simp [height]; exact Nat.le_trans bound (Nat.le_max_right _ _))
      simpa using h

/-- A second test, when needed, reads from the same persistent oracle. -/
def thenTest : Tree Addr → Tree Addr → Tree Addr
  | .done true, y => y
  | .done false, _ => .done false
  | .query i l r, y => .query i (thenTest l y) (thenTest r y)

private theorem then_eval (first second : Tree Addr) (t : Tape Addr) :
    eval t (thenTest first second) = (eval t first && eval t second) := by
  induction first with
  | done b => cases b <;> simp [thenTest, eval]
  | query i l r il ir => cases h : t i <;> simp [thenTest, eval, h, il, ir]

private theorem then_height (first second : Tree Addr) :
    height (thenTest first second) ≤ height first + height second := by
  induction first with
  | done b => cases b <;> simp [thenTest, height]
  | query i l r il ir => simp only [thenTest, height]; omega

def batch {Coin : Type} (test : Coin → Tree Addr) : List Coin → Tree Addr
  | [] => .done true
  | c :: cs => thenTest (test c) (batch test cs)

theorem batch_eval {Coin : Type} (test : Coin → Tree Addr) (coins : List Coin) (t : Tape Addr) :
    eval t (batch test coins) = coins.all (fun c => eval t (test c)) := by
  induction coins with
  | nil => rfl
  | cons c cs ih => simp [batch, then_eval, ih]

theorem batch_height {Coin : Type} (test : Coin → Tree Addr) (coins : List Coin) (q : Nat)
    (bound : ∀ c ∈ coins, height (test c) ≤ q) : height (batch test coins) ≤ coins.length * q := by
  induction coins with
  | nil => simp [batch, height]
  | cons c cs ih =>
    have tail := ih (fun x hx => bound x (by simp [hx]))
    have head := bound c (by simp)
    have both := then_height (test c) (batch test cs)
    simp only [batch, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- If a pool's u-th integer moment beats a common pointwise ceiling, one
    of its entries exceeds that ceiling. Coin-space denominators can be
    absorbed into the numerators before applying this statement. -/
theorem large_moment (xs : List Nat) (u ceiling : Nat)
    (large : xs.length * ceiling ^ u < (xs.map (fun x => x^u)).sum) :
    ∃ x ∈ xs, ceiling < x := by
  induction xs with
  | nil => simp at large
  | cons x xs ih =>
    by_cases high : ceiling < x
    · exact ⟨x, by simp, high⟩
    · have low := Nat.pow_le_pow_left (Nat.le_of_not_gt high) u
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul, List.map_cons, List.sum_cons] at large
      have tail := ih (by omega)
      obtain ⟨y, hy, bound⟩ := tail
      exact ⟨y, by simp [hy], bound⟩

end SampledProofOracle
