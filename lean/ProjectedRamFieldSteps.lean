import Std

namespace ProjectedRamFieldSteps
variable {A C D W V : Type}

/-- The controller includes the program counter. An immutable input operation
is part of the deterministic controller calculation. -/
inductive Op (C A W : Type) where
  | other (next : C)
  | load (address : A) (next : W → C)
  | store (address : A) (value : W) (next : C)

def put [DecidableEq A] (mem : A → W) (address : A) (value : W) : A → W :=
  fun a => if a = address then value else mem a

def exec [DecidableEq A] (mem : A → W) : Op C A W → C × (A → W)
  | .other c => (c, mem)
  | .load a next => (next (mem a), mem)
  | .store a v c => (c, put mem a v)

/-- Local checks on concrete fillings of one canonical row. For a load,
address equality is unconditional. Only its continuation is allowed to use
the promise about retained bits of the incoming value. -/
def stable (pc : C → D) (word : A → W → V) (canon : A → V) :
    Op C A W → Op D A V → Prop
  | .other c, .other d => pc c = d
  | .store a v c, .store b u d => a = b ∧ word a v = u ∧ pc c = d
  | .load a f, .load b g =>
    a = b ∧ ∀ v, word a v = canon b → pc (f v) = g (canon b)
  | _, _ => False

def agrees (pc : C → D) (word : A → W → V)
    (real : C × (A → W)) (canon : D × (A → V)) : Prop :=
  pc real.1 = canon.1 ∧ ∀ a, word a (real.2 a) = canon.2 a

theorem one_step [DecidableEq A] (pc : C → D) (word : A → W → V)
    (mem : A → W) (canon : A → V) (hmem : ∀ a, word a (mem a) = canon a)
    (op : Op C A W) (cop : Op D A V) (h : stable pc word canon op cop) :
    agrees pc word (exec mem op) (exec canon cop) := by
  cases op <;> cases cop <;> simp only [stable] at h
  all_goals try contradiction
  case other.other => exact ⟨h, hmem⟩
  case load.load a f b g =>
    obtain ⟨rfl, continuation⟩ := h
    exact ⟨continuation _ (hmem a), hmem⟩
  case store.store a v c b u d =>
    obtain ⟨rfl, hv, hc⟩ := h
    refine ⟨hc, ?_⟩
    intro x
    by_cases eq : x = a
    · subst x; simpa [exec, put] using hv
    · simpa [exec, put, eq] using hmem x

def run [DecidableEq A] (code : Nat → C → Op C A W) (boot : C × (A → W)) :
    Nat → C × (A → W)
  | 0 => boot
  | i+1 =>
    let state := run code boot i
    exec state.2 (code i state.1)

/-- Arbitrary time-varying controller projections, fixed cell-wise memory
projections, and local stability on just the visited canonical rows. -/
theorem projected_run [DecidableEq A] (pc : Nat → C → D) (word : A → W → V)
    (code : Nat → C → Op C A W) (boot : C × (A → W))
    (acode : Nat → D → Op D A V) (aboot : D × (A → V)) (clock : Nat)
    (init : agrees (pc 0) word boot aboot)
    (checked : ∀ i, i < clock → ∀ c, pc i c = (run acode aboot i).1 →
      stable (pc (i+1)) word (run acode aboot i).2 (code i c)
        (acode i (run acode aboot i).1)) :
    ∀ i ≤ clock, agrees (pc i) word (run code boot i) (run acode aboot i) := by
  intro i
  induction i with
  | zero => exact fun _ => init
  | succ i ih =>
    intro hi
    have prev := ih (Nat.le_of_succ_le hi)
    exact one_step _ _ _ _ prev.2 _ _ (checked i (by omega) _ prev.1)

/-- Flipping coordinate k changes an unsigned word by plus or minus 2^k. -/
theorem flip_difference (x k : Nat) :
    (x ^^^ 2^k) = x + 2^k ∨ x = (x ^^^ 2^k) + 2^k := by
  induction k generalizing x with
  | zero =>
    simp only [Nat.pow_zero]
    have quotient : (x ^^^ 1)/2 = x/2 := by simp [Nat.xor_div_two]
    have parity : (x ^^^ 1)%2 = 1 ↔ x%2 ≠ 1 := by
      rw [Nat.xor_mod_two_eq_one]; simp
    omega
  | succ k ih =>
    have divp : (2^(k+1))/2 = 2^k := by simp [Nat.pow_succ]
    have modp : (2^(k+1))%2 = 0 := by simp [Nat.pow_succ]
    have quotient := Nat.xor_div_two (a:=x) (b:=2^(k+1))
    rw [divp] at quotient
    have parity : (x ^^^ 2^(k+1))%2 = 1 ↔ x%2 = 1 := by
      rw [Nat.xor_mod_two_eq_one, modp]; simp
    have power := Nat.pow_succ 2 k
    have smaller := ih (x/2)
    omega

theorem power_two_mod_three (k : Nat) : (2^k)%3 = 1 ∨ (2^k)%3 = 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    rcases ih with h|h <;> rw [h] <;> decide

/-- A multiple of three is separated from every one-coordinate neighbor
by its residue. The result applies inside any word width containing bit k. -/
theorem flip_changes_divisibility (x k : Nat) (hx : x%3 = 0) :
    (x ^^^ 2^k)%3 ≠ 0 := by
  have d := flip_difference x k
  have p := power_two_mod_three k
  rcases d with h|h
  · rw [h, Nat.add_mod]; omega
  · intro wrong
    have eq := congrArg (fun t : Nat => t%3) h
    simp only at eq
    rw [Nat.add_mod] at eq
    omega

def extendTable (m : Nat) (p : Nat → Nat) (x : Nat) : Nat := if x < m then p x else x

def renamed (m : Nat) (p : Nat → Nat) (x : Nat) : Nat :=
  extendTable m p x ^^^ extendTable m p 0

theorem renamed_zero (m : Nat) (p : Nat → Nat) : renamed m p 0 = 0 := by simp [renamed]

theorem renamed_injective (m : Nat) (p : Nat → Nat)
    (hr : ∀ i < m, p i < m) (hi : ∀ i < m, ∀ j < m, p i = p j → i = j)
    (x y : Nat) (h : renamed m p x = renamed m p y) : x = y := by
  have eq := congrArg (fun z => z ^^^ extendTable m p 0) h
  simp [renamed, Nat.xor_assoc] at eq
  by_cases hx : x < m <;> by_cases hy : y < m
  · exact hi x hx y hy (by simpa [extendTable,hx,hy] using eq)
  · have := hr x hx; simp [extendTable,hx,hy] at eq; omega
  · have := hr y hy; simp [extendTable,hx,hy] at eq; omega
  · simpa [extendTable,hx,hy] using eq

end ProjectedRamFieldSteps
