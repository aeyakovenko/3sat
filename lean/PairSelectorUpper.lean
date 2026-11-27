import Std

/-!
Upper bound 4j+1 for the word-aligned sign-plane catalog F(w, j), for every w and j.
Memory: address i < j holds the positive mask P_i, address j+i holds the negative mask M_i.
Instruction semantics as in the journal's `NineStepSelectorUpper.lean`: a load, an AND
or a binary equality branch costs one; terminal verdicts are free.
-/

namespace PairSelectorUpper

variable {w : Nat}

inductive Code (w : Nat) where
  | halt (yes : Bool)
  | load (address : Nat) (next : BitVec w → Code w)
  | andWord (a b : BitVec w) (next : BitVec w → Code w)
  | branchEq (a b : BitVec w) (yes no : Code w)

def execute (f : Nat → BitVec w) : Code w → Bool × Nat
  | .halt v => (v, 0)
  | .load i k =>
    let r := execute f (k (f i))
    (r.1, r.2 + 1)
  | .andWord a b k =>
    let r := execute f (k (a &&& b))
    (r.1, r.2 + 1)
  | .branchEq a b yes no =>
    let r := if a = b then execute f yes else execute f no
    (r.1, r.2 + 1)

/-- Check the remaining pairs for overlap only: four instructions per pair. -/
def rest (j : Nat) : List Nat → Code w
  | [] => .halt true
  | i :: is => .load i fun p => .load (j+i) fun m => .andWord p m fun t =>
      .branchEq t 0#w (rest j is) (.halt false)

/-- Pairs still owe the "some negative mask is not all ones" condition. -/
def pend (j : Nat) : List Nat → Code w
  | [] => .halt false
  | i :: is => .load (j+i) fun m =>
      .branchEq m (BitVec.allOnes w)
        (.load i fun p => .branchEq p 0#w (pend j is) (.halt false))
        (.load i fun p => .andWord p m fun t => .branchEq t 0#w (rest j is) (.halt false))

def program (j : Nat) : Code w := pend j (List.range j)

theorem and_allOnes' (p : BitVec w) : p &&& BitVec.allOnes w = p := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_and, BitVec.getLsbD_allOnes, hi]

theorem rest_spec (f : Nat → BitVec w) (j : Nat) (l : List Nat) :
    ((execute f (rest j l)).1 = true ↔ ∀ i ∈ l, f i &&& f (j+i) = 0#w) ∧
    (execute f (rest j l)).2 ≤ 4 * l.length := by
  induction l with
  | nil => simp [rest, execute]
  | cons i is ih =>
    by_cases h : f i &&& f (j+i) = 0#w
    · simp only [rest, execute, h, if_true, List.length_cons, List.mem_cons, forall_eq_or_imp,
        true_and]
      exact ⟨ih.1, by have := ih.2; omega⟩
    · simp only [rest, execute, h, if_false, List.length_cons, List.mem_cons, forall_eq_or_imp,
        false_and, Bool.false_eq_true]
      exact ⟨by first | trivial | exact Iff.rfl | simp, by omega⟩

theorem pend_spec (f : Nat → BitVec w) (j : Nat) (l : List Nat) :
    ((execute f (pend j l)).1 = true ↔
      (∀ i ∈ l, f i &&& f (j+i) = 0#w) ∧ (∃ i ∈ l, f (j+i) ≠ BitVec.allOnes w)) ∧
    (execute f (pend j l)).2 ≤ 4 * l.length + 1 := by
  induction l with
  | nil => simp [pend, execute]
  | cons i is ih =>
    by_cases hm : f (j+i) = BitVec.allOnes w
    · by_cases hp : f i = 0#w
      · have hz : f i &&& f (j+i) = 0#w := by simp [hp]
        simp only [pend, execute, hm, hp, if_true, List.length_cons]
        refine ⟨?_, by have := ih.2; omega⟩
        rw [ih.1]
        constructor
        · rintro ⟨h1, k, hk, hk2⟩
          refine ⟨fun x hx => ?_, k, List.mem_cons_of_mem _ hk, hk2⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hz
          · exact h1 x hx
        · rintro ⟨h1, k, hk, hk2⟩
          refine ⟨fun x hx => h1 x (List.mem_cons_of_mem _ hx), ?_⟩
          rcases List.mem_cons.mp hk with rfl | hk
          · exact absurd hm hk2
          · exact ⟨k, hk, hk2⟩
      · have hnz : ¬ (f i &&& f (j+i) = 0#w) := by
          rw [hm, and_allOnes']; exact hp
        simp only [pend, execute, hm, hp, if_true, if_false, List.length_cons]
        refine ⟨?_, by omega⟩
        constructor
        · intro hfalse; exact absurd hfalse (by simp)
        · rintro ⟨h1, _⟩
          exact absurd (h1 i List.mem_cons_self) hnz
    · by_cases ht : f i &&& f (j+i) = 0#w
      · simp only [pend, execute, hm, ht, if_true, if_false, List.length_cons]
        have hr := rest_spec f j is
        refine ⟨?_, by have := hr.2; omega⟩
        rw [hr.1]
        constructor
        · intro h1
          refine ⟨fun x hx => ?_, i, List.mem_cons_self, hm⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ht
          · exact h1 x hx
        · rintro ⟨h1, _⟩
          exact fun x hx => h1 x (List.mem_cons_of_mem _ hx)
      · simp only [pend, execute, hm, ht, if_false, List.length_cons]
        refine ⟨?_, by omega⟩
        constructor
        · intro hfalse; exact absurd hfalse (by simp)
        · rintro ⟨h1, _⟩
          exact absurd (h1 i List.mem_cons_self) ht

/-- Satisfiability of F(w, j) as existence of an assignment, one w-bit block per pair. -/
def hasModel (f : Nat → BitVec w) (j : Nat) : Prop :=
  ∃ x : Nat → BitVec w, (∀ i < j, f i &&& x i = f i ∧ f (j+i) &&& x i = 0#w) ∧
    ∃ i < j, x i ≠ 0#w

def fits (f : Nat → BitVec w) (j : Nat) : Prop :=
  (∀ i < j, f i &&& f (j+i) = 0#w) ∧ ∃ i < j, f (j+i) ≠ BitVec.allOnes w

theorem semantic (f : Nat → BitVec w) (j : Nat) : hasModel f j ↔ fits f j := by
  constructor
  · rintro ⟨x, hx, i, hi, hxi⟩
    refine ⟨fun k hk => ?_, i, hi, ?_⟩
    · obtain ⟨h1, h2⟩ := hx k hk
      apply BitVec.eq_of_getLsbD_eq
      intro b hb
      have e1 := congrArg (fun v => v.getLsbD b) h1
      have e2 := congrArg (fun v => v.getLsbD b) h2
      simp [BitVec.getLsbD_and] at e1 e2 ⊢
      cases h3 : (f k).getLsbD b <;> cases h4 : (f (j+k)).getLsbD b <;>
        cases h5 : (x k).getLsbD b <;> simp_all
    · intro hm
      apply hxi
      obtain ⟨_, h2⟩ := hx i hi
      rw [hm] at h2
      apply BitVec.eq_of_getLsbD_eq
      intro b hb
      have e2 := congrArg (fun v => v.getLsbD b) h2
      simp [BitVec.getLsbD_and, BitVec.getLsbD_allOnes, hb] at e2 ⊢
      exact e2
  · rintro ⟨h1, i, hi, hm⟩
    refine ⟨fun k => ~~~ f (j+k), fun k hk => ⟨?_, ?_⟩, i, hi, ?_⟩
    · apply BitVec.eq_of_getLsbD_eq
      intro b hb
      have e := congrArg (fun v => v.getLsbD b) (h1 k hk)
      simp [BitVec.getLsbD_and, BitVec.getLsbD_not, hb] at e ⊢
      cases h3 : (f k).getLsbD b <;> cases h4 : (f (j+k)).getLsbD b <;> simp_all
    · apply BitVec.eq_of_getLsbD_eq
      intro b hb
      simp [BitVec.getLsbD_and, BitVec.getLsbD_not, hb]
    · intro hz
      apply hm
      apply BitVec.eq_of_getLsbD_eq
      intro b hb
      have e := congrArg (fun v => v.getLsbD b) hz
      simp [BitVec.getLsbD_not, BitVec.getLsbD_allOnes, hb] at e ⊢
      exact e

theorem correct_and_bounded (f : Nat → BitVec w) (j : Nat) :
    ((execute f (program j)).1 = true ↔ hasModel f j) ∧
    (execute f (program (w := w) j)).2 ≤ 4 * j + 1 := by
  have h := pend_spec f j (List.range j)
  refine ⟨?_, by simpa [program] using h.2⟩
  rw [semantic, program, h.1]
  simp [fits, List.mem_range]

/-- The bound is attained: (P0,P1,M0,M1) = (4,4,11,11) at w = 4, j = 2 takes nine steps. -/
theorem attained_nine :
    execute (w := 4)
      (fun i => if i = 0 then 4 else if i = 1 then 4 else if i = 2 then 11 else if i = 3 then 11 else 0)
      (program 2) = (true, 9) := by decide

/-- The bound is attained: the all-zero memory at w = 5, j = 3 takes thirteen steps. -/
theorem attained_thirteen : execute (w := 5) (fun _ => 0) (program 3) = (true, 13) := by decide

end PairSelectorUpper

#print axioms PairSelectorUpper.correct_and_bounded
#print axioms PairSelectorUpper.attained_nine
#print axioms PairSelectorUpper.attained_thirteen
