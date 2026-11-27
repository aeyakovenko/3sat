import Std

namespace PermutationLapReplay

variable {Addr Word Pos Reg : Type}

/-- Existentially select the row of the preceding lap at the requested address. -/
def retrieved (row : Pos → Addr × Word → Prop) (a : Addr) (w : Word) : Prop :=
  ∃ t, row t (a, w)

theorem exact_retrieval (row : Pos → Addr × Word → Prop) (actual : Pos → Addr × Word)
    (exactRows : ∀ t v, row t v ↔ v = actual t)
    (inv : Addr → Pos) (inverseLeft : ∀ i, inv (actual i).1 = i)
    (inverseRight : ∀ a, (actual (inv a)).1 = a) (a : Addr) (w : Word) :
    retrieved row a w ↔ w = (actual (inv a)).2 := by
  constructor
  · rintro ⟨t, h⟩
    have e := (exactRows t (a, w)).mp h
    have key : a = (actual t).1 := congrArg Prod.fst e
    have time : inv a = t := (congrArg inv key).trans (inverseLeft t)
    simpa [time] using congrArg Prod.snd e
  · intro hw
    refine ⟨inv a, (exactRows _ _).mpr ?_⟩
    apply Prod.ext
    · exact (inverseRight a).symm
    · exact hw

/-- A bad-certificate path guesses one prior word at each actual local step.
Its address is computed from the evolving state, not from a supplied schedule. -/
inductive Local (address : Reg → Addr) (update : Reg → Word → Reg)
    (read : Addr → Word → Prop) : Nat → Reg → Reg → Prop
  | zero (s : Reg) : Local address update read 0 s s
  | next (s : Reg) (w : Word) (n : Nat) (z : Reg) (valid : read (address s) w)
      (tail : Local address update read n (update s w) z) :
      Local address update read (n+1) s z

def run (address : Reg → Addr) (update : Reg → Word → Reg) (memory : Addr → Word)
    : Nat → Reg → Reg
  | 0, s => s
  | n+1, s => run address update memory n (update s (memory (address s)))

theorem exact_block (address : Reg → Addr) (update : Reg → Word → Reg)
    (read : Addr → Word → Prop) (memory : Addr → Word)
    (exactOld : ∀ a w, read a w ↔ w = memory a) (n : Nat) (s z : Reg) :
    Local address update read n s z ↔ z = run address update memory n s := by
  induction n generalizing s z with
  | zero =>
    constructor
    · intro h
      cases h
      rfl
    · intro h
      exact h ▸ Local.zero s
  | succ n ih =>
    constructor
    · intro h
      cases h with
      | next _ w _ _ valid tail =>
        have e := (exactOld _ _).mp valid
        subst w
        exact (ih _ _).mp tail
    · intro h
      refine Local.next s (memory (address s)) n z ((exactOld _ _).mpr rfl) ?_
      exact (ih _ _).mpr h

/-- Once the preceding lap is exact, forbidding a witnessed endpoint error
also guarantees that the genuine endpoint is reached, with no separate
existential completeness challenge. -/
theorem forbid_bad_endpoint (address : Reg → Addr) (update : Reg → Word → Reg)
    (read : Addr → Word → Prop) (memory : Addr → Word)
    (exactOld : ∀ a w, read a w ↔ w = memory a) (n : Nat) (s header : Reg) :
    (¬ ∃ z, Local address update read n s z ∧ z ≠ header) ↔
    run address update memory n s = header := by
  constructor
  · intro noBad
    apply Classical.byContradiction
    intro unequal
    exact noBad ⟨_, (exact_block address update read memory exactOld n s _).mpr rfl, unequal⟩
  · intro equal
    rintro ⟨z, localRun, unequal⟩
    exact unequal (((exact_block address update read memory exactOld n s z).mp localRun).trans equal)

#print axioms exact_retrieval
#print axioms forbid_bad_endpoint

end PermutationLapReplay
