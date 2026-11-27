import Std

namespace OneWatchedWorkAddress

abbrev Memory := Nat → Nat
abbrev SetCode := Nat → Bool

inductive Op (C : Type) where
  | pure (next : C)
  | store (addr value : Nat) (next : C)
  | load (addr : Nat) (next : Nat → C)

def write (mem : Memory) (addr value : Nat) : Memory :=
  fun a => if a = addr then value else mem a

structure Trace (C : Type) where
  finish : C
  hot : List Nat
  errors : List Nat

def mark (b : Bool) (a : Nat) (xs : List Nat) : List Nat :=
  if b then a :: xs else xs

def run {C : Type} (op : C → Op C) (keep : SetCode) : Nat → C → Memory → Trace C
  | 0, c, _ => ⟨c, [], []⟩
  | n+1, c, mem =>
    match op c with
    | .pure next => run op keep n next mem
    | .store a v next => run op keep n next (write mem a v)
    | .load a next =>
      let value := mem a
      let reply := if keep a then value else 0
      let tail := run op keep n (next reply) mem
      ⟨tail.finish, mark (reply != 0) a tail.hot,
        mark (!keep a && value != 0) a tail.errors⟩

def allWords : SetCode := fun _ => true

private theorem complete {C : Type} (op : C → Op C) (keep : SetCode) (n : Nat)
    (c : C) (mem : Memory)
    (cover : ∀ a ∈ (run op allWords n c mem).hot, keep a = true) :
    run op keep n c mem = run op allWords n c mem := by
  induction n generalizing c mem with
  | zero => rfl
  | succ n ih =>
    cases h : op c with
    | pure next => simpa [run, h] using ih next mem (by simpa [run, h] using cover)
    | store a v next =>
      simpa [run, h] using ih next (write mem a v) (by simpa [run, h] using cover)
    | load a next =>
      by_cases hv : mem a = 0
      · simp [run, h, allWords, hv, mark] at cover ⊢
        rw [ih (next 0) mem cover]
        simp
      · have hk : keep a = true := cover a (by simp [run, h, allWords, hv, mark])
        have ht : ∀ b ∈ (run op allWords n (next (mem a)) mem).hot, keep b = true := by
          intro b hb
          exact cover b (by simp [run, h, allWords, hv, mark, hb])
        simp [run, h, allWords, hk, hv, mark, ih _ _ ht]

private theorem genuine_if_clear {C : Type} (op : C → Op C) (keep : SetCode)
    (n : Nat) (c : C) (mem : Memory) (clear : (run op keep n c mem).errors = []) :
    (run op keep n c mem).finish = (run op allWords n c mem).finish := by
  induction n generalizing c mem with
  | zero => rfl
  | succ n ih =>
    cases h : op c with
    | pure next => simpa [run, h] using ih next mem (by simpa [run, h] using clear)
    | store a v next =>
      simpa [run, h] using ih next (write mem a v) (by simpa [run, h] using clear)
    | load a next =>
      cases hk : keep a with
      | true =>
        simp [run, h, hk, mark] at clear
        simpa [run, h, hk, allWords] using ih (next (mem a)) mem clear
      | false =>
        by_cases hv : mem a = 0
        · simp [run, h, hk, hv, mark] at clear
          simpa [run, h, hk, allWords, hv] using ih (next 0) mem clear
        · simp [run, h, hk, hv, mark] at clear

private theorem genuine_clear {C : Type} (op : C → Op C) (n : Nat) (c : C)
    (mem : Memory) : (run op allWords n c mem).errors = [] := by
  induction n generalizing c mem with
  | zero => rfl
  | succ n ih =>
    cases h : op c with
    | pure next => simpa [run, h] using ih next mem
    | store a v next => simpa [run, h] using ih next (write mem a v)
    | load a next => simpa [run, h, allWords, mark] using ih (next (mem a)) mem

/-- Operational monitor. Outside the proposed set only the single watched word
is retained. The mutable store argument contains values for retained slots. -/
def watched {C : Type} (op : C → Op C) (keep : SetCode) (a : Nat) :
    Nat → C → Memory → Nat → Bool
  | 0, _, _, _ => false
  | n+1, c, slots, word =>
    match op c with
    | .pure next => watched op keep a n next slots word
    | .store b v next =>
      watched op keep a n next (if keep b then write slots b v else slots)
        (if a = b then v else word)
    | .load b next =>
      ((!keep b && a == b && word != 0) ||
        watched op keep a n (next (if keep b then slots b else 0)) slots word)

/-- The one-word monitor detects exactly the selected errors of the projected trace. -/
theorem watched_iff {C : Type} (op : C → Op C) (keep : SetCode) (a n : Nat)
    (c : C) (mem slots : Memory)
    (agree : ∀ b, keep b = true → slots b = mem b) :
    watched op keep a n c slots (mem a) = true ↔
      a ∈ (run op keep n c mem).errors := by
  induction n generalizing c mem slots with
  | zero => simp [run, watched]
  | succ n ih =>
    cases h : op c with
    | pure next => simpa [watched, run, h] using ih next mem slots agree
    | store b v next =>
      have hg : ∀ j, keep j = true →
          (if keep b then write slots b v else slots) j = (write mem b v) j := by
        intro j hj
        by_cases hsame : j = b
        · subst j
          simp [hj, write]
        · cases hb : keep b <;> simp [hb, write, hsame, agree j hj]
      simpa [run, watched, h, write] using ih next (write mem b v) _ hg
    | load b next =>
      cases hk : keep b with
      | true =>
        simpa [watched, run, h, hk, agree b hk, mark] using ih (next (mem b)) mem slots agree
      | false =>
        have ht := ih (next 0) mem slots agree
        by_cases heq : a = b
        · subst b
          by_cases hv : mem a = 0
          · simpa [watched, run, h, hk, hv, mark] using (hv ▸ ht)
          · simp [watched, run, h, hk, hv, mark]
        · by_cases hv : mem b = 0 <;> simp [watched, run, h, hk, heq, hv, mark, ht]

/-- A single monitored address suffices after an arbitrary support guess. -/
theorem projected_game {C : Type} (op : C → Op C) (n : Nat) (c : C) (mem : Memory)
    (pass : C → Prop) (allowed : SetCode → Prop)
    (support : ∃ keep, allowed keep ∧
      ∀ a ∈ (run op allWords n c mem).hot, keep a = true) :
    pass (run op allWords n c mem).finish ↔
    ∀ keep, allowed keep → ∃ a : Nat,
      pass (run op keep n c mem).finish ∨ a ∈ (run op keep n c mem).errors := by
  constructor
  · intro yes keep _
    cases h : (run op keep n c mem).errors with
    | nil => exact ⟨0, Or.inl ((genuine_if_clear op keep n c mem h) ▸ yes)⟩
    | cons a tail => exact ⟨a, Or.inr (by simp [h])⟩
  · intro game
    obtain ⟨keep, hk, cover⟩ := support
    obtain ⟨a, res⟩ := game keep hk
    rw [complete op keep n c mem cover, genuine_clear op n c mem] at res
    simpa using res

/-- With doubled exponents the endpoint recurrence subtracts one until a
negative floor is reached. For the row selector the floor is 2*(1-A). -/
theorem endpoint_drop (floor u : Int) (hf : floor ≤ -1) (hu : 0 ≤ u) :
    max (u - 1) floor = u - 1 := by omega

private def certificateStep (floor : Int) : Nat → Int → Int
  | 0, u => u
  | n+1, u => certificateStep floor n (max (u-1) floor)

theorem finite_endpoint_crossing (floor : Int) (hf : floor ≤ -1) (w : Nat) :
    certificateStep floor (w+1) (Int.ofNat w) = -1 := by
  induction w with
  | zero => simp [certificateStep] <;> omega
  | succ w ih =>
    have hz : 0 ≤ Int.ofNat (w+1) := Int.ofNat_zero_le _
    rw [certificateStep, endpoint_drop floor (Int.ofNat (w+1)) hf hz]
    have he : Int.ofNat (w+1) - 1 = Int.ofNat w := by simp
    rw [he]
    exact ih

end OneWatchedWorkAddress
