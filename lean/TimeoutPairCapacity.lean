import Std

namespace TimeoutPairCapacity

/-- Patterns record whether a possible nonempty witness set hits two queried sets. -/
structure Pattern where
  hitsA : Bool
  hitsB : Bool
  deriving DecidableEq

def join (p q : Pattern) : Pattern :=
  ⟨p.hitsA || q.hitsA, p.hitsB || q.hitsB⟩

inductive Reply where
  | noA | noB | timeoutBoth

def compatible : Reply → Pattern → Prop
  | .noA, p => p.hitsA = false
  | .noB, p => p.hitsB = false
  | .timeoutBoth, p => p.hitsA = p.hitsB

/-- Every all-negative reply used by the adversary remains legal on the
    union of two witness sets that were each compatible with it. -/
theorem compatible_join (r : Reply) (p q : Pattern)
    (hp : compatible r p) (hq : compatible r q) : compatible r (join p q) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  cases r <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [join, compatible]

theorem merge_cross : compatible .timeoutBoth
    (join ⟨false,true⟩ ⟨true,false⟩) := rfl

/-- z,a,b,c are the numbers of disjoint packs of types 00,01,10,11. -/
theorem binary_count (z a b c : Nat) :
    z+a+b+c ≤ 2 * max (max (z+a) (z+b)) (z+c+min a b) := by omega

theorem ternary_count (z a b c : Nat) :
    z+a+b+c ≤ 3 * max (max (z+a) (z+b)) (z+c) := by omega

/-- Interleaving pair queries and single-point checks cannot improve the
    capacity inequality along the adversary's empty-instance transcript. -/
inductive Remaining (base size : Nat) : Nat → Nat → Nat → Prop where
  | start : Remaining base size 0 0 size
  | pair (past : Remaining base size q u r) (keep : r ≤ base * s) :
      Remaining base size (q+1) u s
  | point (past : Remaining base size q u r) (keep : r ≤ s+1) :
      Remaining base size q (u+1) s

theorem capacity {base size q u r : Nat} (hb : 1 ≤ base)
    (trace : Remaining base size q u r) : size ≤ base^q * (r+u) := by
  induction trace with
  | start => simp
  | @pair q u r s _ keep ih =>
    have hu : u ≤ base * u := by simpa using Nat.mul_le_mul_right u hb
    have h : r+u ≤ base*(s+u) := by rw [Nat.mul_add]; omega
    calc
      _ ≤ base^q * (r+u) := ih
      _ ≤ base^q * (base*(s+u)) := Nat.mul_le_mul_left _ h
      _ = base^(q+1)*(s+u) := by rw [Nat.pow_succ, Nat.mul_assoc]
  | @point q u r s _ keep ih =>
    exact Nat.le_trans ih (Nat.mul_le_mul_left _ (by omega))

theorem negative_transcript {base size q u : Nat} (hb : 1 ≤ base)
    (done : Remaining base size q u 0) : size ≤ base^q * u := by
  simpa using capacity hb done

end TimeoutPairCapacity
