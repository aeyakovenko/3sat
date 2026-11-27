import Std

/-! A finite counting lemma for the prime-slot obstruction. One step
represents a block of input bits and has one successor per possible word.
The list retains multiplicities when distinct words reach the same state.
A state of credit zero is dead. Time-dependent transitions can store the
layer in the state. -/
namespace PrimeSlotProgress

structure Process (α : Type) (choices credits : Nat) where
  next : α → List α
  credit : α → Nat
  arity : ∀ s, (next s).length = choices
  bounded : ∀ s, credit s ≤ credits
  dead : ∀ s, credit s = 0 → ∀ t ∈ next s, credit t = 0
  progress : ∀ s, 0 < credit s → ∃ t ∈ next s, credit t < credit s

namespace Process

variable {α : Type} {choices credits : Nat}

def walks (p : Process α choices credits) : Nat → α → List α
  | 0, s => [s]
  | n + 1, s => (p.next s).flatMap (p.walks n)

private theorem sum_const (xs : List α) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]

theorem walks_length (p : Process α choices credits) (n : Nat) (s : α) :
    (p.walks n s).length = choices ^ n := by
  induction n generalizing s with
  | zero => simp [walks]
  | succ n ih =>
    simp only [walks, List.length_flatMap, ih, sum_const, p.arity]
    rw [Nat.pow_succ, Nat.mul_comm]

theorem walks_add (p : Process α choices credits) (a b : Nat) (s : α) :
    p.walks (a + b) s = (p.walks a s).flatMap (p.walks b) := by
  induction a generalizing s with
  | zero => simp [walks]
  | succ a ih =>
    have compose : p.walks (a + b) = fun x => (p.walks a x).flatMap (p.walks b) :=
      funext ih
    simp only [Nat.succ_add, walks, List.flatMap_assoc, compose]

private theorem walk_from_dead (p : Process α choices credits) (n : Nat)
    {s t : α} (hs : p.credit s = 0) (ht : t ∈ p.walks n s) :
    p.credit t = 0 := by
  induction n generalizing s with
  | zero =>
    have same : t = s := List.mem_singleton.mp ht
    simpa [same] using hs
  | succ n ih =>
    obtain ⟨u, hu, ht'⟩ := List.mem_flatMap.mp ht
    exact ih (p.dead s hs u hu) ht'

/-- Choosing one strict improvement from each live state yields at least
one dead continuation of any length at least its current credit. -/
theorem reaches_dead (p : Process α choices credits) (nonempty : 0 < choices)
    (n : Nat) (s : α) (budget : p.credit s ≤ n) :
    ∃ t ∈ p.walks n s, p.credit t = 0 := by
  induction n generalizing s with
  | zero => exact ⟨s, by simp [walks], by omega⟩
  | succ n ih =>
    have successor : ∃ u ∈ p.next s, p.credit u ≤ n := by
      by_cases hs : p.credit s = 0
      · have hn : p.next s ≠ [] := by
          intro empty
          have count := p.arity s
          simp [empty] at count
          omega
        obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hn
        exact ⟨u, hu, by simp [p.dead s hs u hu]⟩
      · obtain ⟨u, hu, smaller⟩ := p.progress s (by omega)
        exact ⟨u, hu, by omega⟩
    obtain ⟨u, hu, within⟩ := successor
    obtain ⟨t, htu, zero⟩ := ih u within
    exact ⟨t, List.mem_flatMap.mpr ⟨u, hu, htu⟩, zero⟩

private theorem live_flatMap_bound (f : α → List α) (live : α → Bool)
    (factor : Nat) (cap : ∀ x, (f x).countP live ≤ if live x then factor else 0)
    (xs : List α) : (xs.flatMap f).countP live ≤ xs.countP live * factor := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := cap x
    rw [List.flatMap_cons, List.countP_append, List.countP_cons]
    cases h : live x <;>
      simp only [h, Bool.false_eq_true, if_false, if_true] at hx <;>
      simp [h, Nat.add_mul] <;> omega

/-- Of the choices^(chunks * credits) uniformly weighted extensions,
at most (choices^credits - 1)^chunks remain live. For B-bit blocks
the number of choices is 2^B. -/
theorem surviving_extensions (p : Process α choices credits) (nonempty : 0 < choices)
    (chunks : Nat) (s : α) :
    (p.walks (chunks * credits) s).countP (fun t => decide (0 < p.credit t))
      ≤ (choices ^ credits - 1) ^ chunks := by
  let live (t : α) : Bool := decide (0 < p.credit t)
  change (p.walks (chunks * credits) s).countP live ≤ _
  have cap (x : α) : (p.walks credits x).countP live ≤
      if live x then choices ^ credits - 1 else 0 := by
    by_cases hs : p.credit x = 0
    · have allDead : (p.walks credits x).countP live = 0 := by
        apply List.countP_eq_zero.mpr
        intro t ht
        simp [live, p.walk_from_dead credits hs ht]
      simp [live, hs, allDead]
    · have pos : 0 < p.credit x := by omega
      obtain ⟨t, ht, dead⟩ := p.reaches_dead nonempty credits x (p.bounded x)
      have strict : (p.walks credits x).countP live ≠ (p.walks credits x).length := by
        intro eq
        have yes := List.countP_eq_length.mp eq t ht
        simp [live, dead] at yes
      have le : (p.walks credits x).countP live ≤ (p.walks credits x).length :=
        List.countP_le_length
      rw [p.walks_length] at le strict
      have active : live x = true := by simp [live, pos]
      rw [if_pos active]
      omega
  induction chunks with
  | zero => simp [walks, List.countP_cons]; split <;> omega
  | succ j ih =>
    rw [Nat.succ_mul, p.walks_add, Nat.pow_succ]
    exact Nat.le_trans (live_flatMap_bound _ live _ cap _) (Nat.mul_le_mul_right _ ih)

end Process
end PrimeSlotProgress
