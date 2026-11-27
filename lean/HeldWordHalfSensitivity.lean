import Std

namespace HeldWordHalfSensitivity

inductive Mode where
  | zero | one | source
  deriving DecidableEq

def mode (k : Fin 16) : Mode :=
  match k.val with
  | 0 | 15 => .source
  | 3 | 4 | 5 | 8 | 10 | 13 | 14 => .one
  | _ => .zero

def value (source : Bool) : Mode → Bool
  | .zero => false
  | .one => true
  | .source => source

def neighbor (k : Fin 16) (j : Fin 4) : Fin 16 :=
  ⟨(k.val ^^^ (2 ^ j.val)) % 16, Nat.mod_lt _ (by decide)⟩

def changed (source : Bool) (k : Fin 16) (j : Fin 4) : Bool :=
  value source (mode (neighbor k j)) != value source (mode k)

theorem local_halves : ∀ k : Fin 16, ∀ s : Bool,
    2 ≤ (List.finRange 4).countP (changed s k) := by decide

theorem base_exact : ∀ s : Bool, (List.finRange 4).countP (changed s 0) = 2 := by decide

theorem source_keys : ∀ k : Fin 16, mode k = .source ↔ k = 0 ∨ k = 15 := by decide

def physicalFlips (copies : Nat) (gs : List (Fin 4)) : List (Fin 4) :=
  gs.flatMap (List.replicate copies)

private theorem count_replicate {α : Type} (p : α → Bool) (n : Nat) (x : α) :
    (List.replicate n x).countP p = if p x then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih => cases h : p x <;> simp [List.replicate_succ, List.countP_cons, ih, h]

theorem lifted_count (c : Nat) (gs : List (Fin 4)) (p : Fin 4 → Bool) :
    (physicalFlips c gs).countP p = c * gs.countP p := by
  induction gs with
  | nil => simp [physicalFlips]
  | cons i gs ih =>
    simp only [physicalFlips, List.flatMap_cons, List.countP_append] at ih ⊢
    rw [count_replicate, ih]
    cases h : p i <;> simp [List.countP_cons, h, Nat.mul_add, Nat.add_comm]

theorem physical_halves (c : Nat) (k : Fin 16) (s : Bool) :
    c * 2 ≤ (physicalFlips c (List.finRange 4)).countP (changed s k) := by
  rw [lifted_count]
  exact Nat.mul_le_mul_left c (local_halves k s)

theorem opposite_counts (ans : List Bool) :
    ans.countP (fun b => b != true) + ans.countP (fun b => b != false) = ans.length := by
  induction ans with
  | nil => decide
  | cons x xs ih =>
    cases x <;> simp [List.countP_cons] at * <;> omega

/-- The numerical part of the UNSAT certificate: a strict majority of actual
    YES neighbors is equivalent to a false source under majority reversals. -/
theorem majority_detects_false (s : Bool) (ans : List Bool)
    (flip : ans.length < 2 * ans.countP (fun b => b != s)) :
    s = false ↔ ans.length < 2 * ans.countP (fun b => b != false) := by
  cases s with
  | false => exact ⟨fun _ => flip, fun _ => rfl⟩
  | true =>
    have counts := opposite_counts ans
    constructor
    · intro h; cases h
    · intro h; omega

#print axioms physical_halves
#print axioms majority_detects_false

end HeldWordHalfSensitivity
