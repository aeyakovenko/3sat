import Std

namespace MixedPrefixDeadlineCapacity

/-- Leaves carry the number of selected positive inputs accepted there. -/
inductive Tree where
  | yes (count : Nat)
  | no
  | data (next : Tree)
  | cmp (left right : Tree)

def hasNegative : Tree → Bool
  | .yes _ => false
  | .no => true
  | .data t => hasNegative t
  | .cmp l r => hasNegative l || hasNegative r

/-- The number of positives already accepted by the stated remaining clock. -/
def fast : Nat → Tree → Nat
  | _, .yes n => n
  | _, .no => 0
  | 0, .data _ | 0, .cmp _ _ => 0
  | n+1, .data t => fast n t
  | n+1, .cmp l r => fast n l + fast n r

/-- An all-positive child can be made an immediate accepting leaf and padded. -/
def valid (A : Nat → Nat) (fuel data : Nat) (t : Tree) : Prop :=
  (hasNegative t = false → fast fuel t ≤ A data) ∧
    match fuel,t with
    | n+1, .data s => valid A n (data+1) s
    | n+1, .cmp l r => valid A n data l ∧ valid A n data r
    | _,_ => True

theorem pure_bound {A : Nat → Nat} {fuel data : Nat} {t : Tree}
    (ok : valid A fuel data t) (pureNode : hasNegative t = false) :
    fast fuel t ≤ A data := by
  cases fuel <;> cases t <;> exact ok.1 pureNode

def B (A : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, data =>
    let child := B A n data
    max (B A n (data+1)) (max (2*child) (A data+child))

theorem mixed_bound (A : Nat → Nat) (fuel data : Nat) (t : Tree)
    (ok : valid A fuel data t) (mixed : hasNegative t = true) :
    fast fuel t ≤ B A fuel data := by
  induction fuel generalizing data t with
  | zero =>
    cases t <;> simp_all [fast,hasNegative,B]
  | succ n ih =>
    cases t with
    | yes k => simp [hasNegative] at mixed
    | no => simp [fast]
    | data t =>
      apply Nat.le_trans (ih _ t ok.2 mixed)
      exact Nat.le_max_left _ _
    | cmp l r =>
      obtain ⟨hl, hr⟩ := ok.2
      have h1 : 2*B A n data ≤ B A (n+1) data :=
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      have h2 : A data+B A n data ≤ B A (n+1) data :=
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      simp only [fast]
      cases bl : hasNegative l <;> cases br : hasNegative r
      · simp [hasNegative,bl,br] at mixed
      · have xp := pure_bound hl bl
        have yp := ih data r hr br
        omega
      · have xp := ih data l hl bl
        have yp := pure_bound hr br
        omega
      · have xp := ih data l hl bl
        have yp := ih data r hr br
        omega

def weights : Nat → Nat
  | 4 => 1 | 5 => 8 | 6 => 18 | 7 => 36 | _ => 0

theorem root_value : B weights 8 0 = 36 := by decide
theorem seven_step_sibling_value : B weights 1 5 = 8 := by decide

end MixedPrefixDeadlineCapacity
