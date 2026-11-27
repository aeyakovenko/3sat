import Std

namespace DLMSTHistoryTransfer

variable {A V : Type} [DecidableEq A] [DecidableEq V]

def put (m : A → V) (a : A) (v : V) : A → V :=
  fun t => if t = a then v else m t

inductive Op (A V : Type)
  | read (address : A)
  | write (address : A) (value : V)

def writes : List (Op A V) → Nat
  | [] => 0
  | .read _ :: tail => writes tail
  | .write _ _ :: tail => writes tail + 1

/-- Disagreements between the current value and its last read at this address. -/
def changes : List (Op A V) → (A → V) → (A → V) → Nat
  | [], _, _ => 0
  | .write a v :: tail, mem, seen => changes tail (put mem a v) seen
  | .read a :: tail, mem, seen =>
      (if mem a = seen a then 0 else 1) + changes tail mem (put seen a (mem a))

/-- Each value change spends a prior write at its own address. Extra entries
in the initial list of pending changes give the version with initial credit. -/
theorem changes_le (ops : List (Op A V)) (mem seen : A → V) (pending : List A)
    (covered : ∀ t, mem t ≠ seen t → t ∈ pending) :
    changes ops mem seen ≤ writes ops + pending.length := by
  induction ops generalizing mem seen pending with
  | nil => simp [changes, writes]
  | cons op tail ih =>
    cases op with
    | write a v =>
      have cover : ∀ t, put mem a v t ≠ seen t → t ∈ a :: pending := by
        intro t mismatch
        by_cases h : t = a
        · simp [h]
        · have hm : mem t ≠ seen t := by simpa [put, h] using mismatch
          exact List.mem_cons_of_mem a (covered t hm)
      have bound := ih (put mem a v) seen (a :: pending) cover
      simp only [changes, writes, List.length_cons] at bound ⊢
      omega
    | read a =>
      have cover : ∀ t, mem t ≠ put seen a (mem a) t → t ∈ pending.erase a := by
        intro t mismatch
        by_cases h : t = a
        · subst t
          simp [put] at mismatch
        · apply (List.mem_erase_of_ne h).mpr
          exact covered t (by simpa [put, h] using mismatch)
      have bound := ih mem (put seen a (mem a)) (pending.erase a) cover
      simp only [changes, writes]
      by_cases h : mem a = seen a
      · simp only [if_pos h, Nat.zero_add]
        have hlen := List.length_erase_le (l := pending) (a := a)
        omega
      · have ha := covered a h
        have hp : pending.length > 0 := by
          cases pending with
          | nil => simp at ha
          | cons => simp
        rw [List.length_erase_of_mem ha] at bound
        simp [h]
        omega

theorem known_initial_budget (ops : List (Op A V)) (initial : A → V) :
    changes ops initial initial ≤ writes ops := by
  simpa using changes_le ops initial initial [] (by simp)

def blockAnswer (a b c d : Bool) : Bool := (a && b) ^^ (c && d)

theorem balanced_blocks :
    [true, true, false, false].count true = [true, false, true, false].count true ∧
    [true, true, false, false].count false = [true, false, true, false].count false ∧
    blockAnswer true true false false ≠ blockAnswer true false true false := by decide

/-- Satisfiability after pinning one antecedent from each bank and one
false consequent. -/
def pinned {I J K : Type} (H : I → J → K → Prop) (i : I) (j : J) (k : K) : Prop :=
  ∃ (X : I → Prop) (Y : J → Prop) (Z : K → Prop),
    X i ∧ Y j ∧ ¬ Z k ∧ (∀ a b c, H a b c → X a → Y b → Z c)

theorem pin_recovers_membership {I J K : Type} (H : I → J → K → Prop)
    (i : I) (j : J) (k : K) : pinned H i j k ↔ ¬ H i j k := by
  constructor
  · rintro ⟨X,Y,Z,xi,yj,zk,models⟩ edge
    exact zk (models i j k edge xi yj)
  · intro absent
    refine ⟨fun a => a = i, fun b => b = j, fun c => c ≠ k, rfl, rfl, ?_, ?_⟩
    · exact fun bad => bad rfl
    · intro a b c h ha hb hc
      subst a
      subst b
      subst c
      exact absent h

end DLMSTHistoryTransfer
