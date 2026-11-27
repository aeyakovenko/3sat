import Std

namespace NativeCohortClauseClocks

abbrev Nibble := BitVec 4
abbrev Label := Fin 8

structure File where
  p : Nibble
  q : Nibble
  m : Nibble
  n : Nibble

def target (u v : Label) : File :=
  let p := BitVec.ofNat 4 (4 + u.val)
  let q := BitVec.ofNat 4 (4 + v.val)
  ⟨p,q,~~~p,~~~q⟩

def read (f : File) (address : Nibble) : Nibble :=
  match address.toNat with
  | 0 => f.p
  | 1 => f.q
  | 2 => f.m
  | 3 => f.n
  | _ => 0

/-- Native Q's cost from its active loop test through increment, or to rejection.
    The first nine instructions include address generation and the range check.
    This unrolls labels 4 to 23 of BATCH in the executable audit. -/
def record (f : File) : Bool × Nat :=
  let j := f.q &&& f.n
  if j.toNat ≥ 4 then (false,9)
  else
    let shortcut := f.m == 11 && read f j == 4
    let spent := if f.m == 11 then 13 else 12
    if shortcut then (true,14)
    else if f.p &&& f.m != 0 then (false,spent+3)
    else if j != 0 then (false,spent+4)
    else if f.m != 15 then (true,spent+6)
    else if f.n == 15 then (false,spent+6)
    else (true,spent+7)

theorem cohort_cost : ∀ u v : Label,
    record (target u v) = (true, if u.val = 0 then 14 else 18) := by decide +kernel

def remaining : List File → Bool × Nat
  | [] => (true,1)
  | f :: fs =>
    let (ok,t) := record f
    if ok then
      let (next,s) := remaining fs
      (next,t+s)
    else (false,t)

structure Literal (V : Type) where
  name : V
  negated : Bool

def bit (a : V → Bool) (l : Literal V) : Bool := xor (a l.name) l.negated

structure Clause (V : Type) where
  a : Literal V
  b : Literal V
  c : Literal V
  q : Label

def value (a : V → Bool) (s : Clause V) : Bool := bit a s.a || bit a s.b || bit a s.c

def code (u v w : Bool) : Label :=
  ⟨u.toNat + 2*v.toNat + 4*w.toNat, by cases u <;> cases v <;> cases w <;> decide⟩

def encode (a : V → Bool) (s : Clause V) : File :=
  target (code (bit a s.a) (bit a s.b) (bit a s.c)) s.q

theorem code_zero (u v w : Bool) : (code u v w).val = 0 ↔ (u || v || w) = false := by
  cases u <;> cases v <;> cases w <;> decide

theorem encoded_record (a : V → Bool) (s : Clause V) :
    record (encode a s) = (true,14 + if value a s then 4 else 0) := by
  rw [encode,cohort_cost]
  simp only [code_zero]
  change (true, if value a s = false then 14 else 18) = _
  cases value a s <;> rfl

theorem uninterrupted_clock (a : V → Bool) (xs : List (Clause V)) :
    remaining (xs.map (encode a)) =
      (true, 1 + 14*xs.length + 4*(xs.countP (value a))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,remaining,encoded_record,ih,if_true,
      List.length_cons,List.countP_cons,Nat.mul_add,Nat.mul_one]
    cases h : value a x <;> simp [h] <;> omega

end NativeCohortClauseClocks
