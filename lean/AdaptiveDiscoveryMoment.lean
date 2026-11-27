import Std

namespace AdaptiveDiscoveryMoment

/-- When there are n+1 unused tags, list the forecast tag first and the other
    n outcomes in any order. Every outcome has its own continuation. Leaves
    can carry arbitrary records of the actual discovery history. -/
inductive Tree (α : Type) : Nat → Type where
  | leaf (record : α) : Tree α 0
  | step {n : Nat} (hit : Tree α n) (miss : Fin n → Tree α n) : Tree α (n+1)

/-- Each entry corresponds to one full path and counts its successful forecasts. -/
def hitCounts {α : Type} : {n : Nat} → Tree α n → List Nat
  | _, .leaf _ => [0]
  | _, .step (n := n) hit miss =>
    (hitCounts hit).map Nat.succ ++ (List.finRange n).flatMap (fun i => hitCounts (miss i))

def weight (z : Nat) : List Nat → Nat
  | [] => 0
  | h :: rest => z ^ h + weight z rest

def rising (z : Nat) : Nat → Nat
  | 0 => 1
  | n+1 => (z+n) * rising z n

private theorem weight_append (z : Nat) (left right : List Nat) :
    weight z (left ++ right) = weight z left + weight z right := by
  induction left with
  | nil => simp [weight]
  | cons _ _ ih => simp [weight, ih, Nat.add_assoc]

private theorem weight_hit (z : Nat) (hs : List Nat) :
    weight z (hs.map Nat.succ) = z * weight z hs := by
  induction hs with
  | nil => simp [weight]
  | cons _ _ ih => simp [weight, ih, Nat.pow_succ, Nat.mul_add, Nat.mul_comm]

private theorem weight_children {ι : Type} (z m : Nat) (children : ι → List Nat)
    (uniform : ∀ i, weight z (children i) = m) (indices : List ι) :
    weight z (indices.flatMap children) = indices.length * m := by
  induction indices with
  | nil => simp [weight]
  | cons _ _ ih =>
    simp [List.flatMap_cons, weight_append, uniform, ih, Nat.succ_mul, Nat.add_comm]

/-- This is the unnormalized probability generating function under uniform
    completion. Its value does not depend on how earlier outcomes change the
    predictor, the next destination, or the subsequent ordering of misses. -/
theorem exact_moment {α : Type} {n : Nat} (tree : Tree α n) (z : Nat) :
    weight z (hitCounts tree) = rising z n := by
  induction tree with
  | leaf _ => simp [hitCounts, rising, weight]
  | @step n hit miss ihHit ihMiss =>
    simp only [hitCounts, weight_append, weight_hit, ihHit]
    rw [weight_children z (rising z n) (fun i => hitCounts (miss i)) ihMiss]
    simp [rising, Nat.add_mul]

private theorem weight_one (hs : List Nat) : weight 1 hs = hs.length := by
  induction hs with
  | nil => rfl
  | cons _ _ ih => simp [weight, ih, Nat.add_comm]

/-- The normalization is 1·2·...·n, including the empty product at n=0. -/
theorem count_leaves {α : Type} {n : Nat} (tree : Tree α n) :
    (hitCounts tree).length = rising 1 n := by
  simpa [weight_one] using exact_moment tree 1

private theorem tail_weight (hs : List Nat) (z r : Nat) (positive : 0 < z) :
    (hs.countP (fun h => decide (r ≤ h))) * z^r ≤ weight z hs := by
  induction hs with
  | nil => simp [weight]
  | cons h rest ih =>
    by_cases hr : r ≤ h
    · have hp : z^r ≤ z^h := Nat.pow_le_pow_right positive hr
      simp [List.countP_cons, hr, weight, Nat.succ_mul] at *
      omega
    · simp [List.countP_cons, hr, weight]
      omega

theorem count_many_hits {α : Type} {n : Nat} (tree : Tree α n)
    (z r : Nat) (positive : 0 < z) :
    ((hitCounts tree).countP (fun h => decide (r ≤ h))) * z^r ≤ rising z n := by
  rw [← exact_moment tree z]
  exact tail_weight (hitCounts tree) z r positive

end AdaptiveDiscoveryMoment
