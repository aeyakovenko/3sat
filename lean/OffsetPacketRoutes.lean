import Std

namespace OffsetPacketRoutes

/-- The graph unfolded at one source, keeping distinct outgoing edge labels. -/
inductive BinaryRoutes where
  | stop
  | fork (zero one : BinaryRoutes)

/-- Length-h codes covered by terminal prefixes of length at most h. -/
def covered : BinaryRoutes → Nat → Nat
  | .stop, h => 2 ^ h
  | .fork _ _, 0 => 0
  | .fork left right, h + 1 => covered left h + covered right h

theorem prefix_capacity (paths : BinaryRoutes) (h : Nat) :
    covered paths h ≤ 2 ^ h := by
  induction h generalizing paths with
  | zero => cases paths <;> simp [covered]
  | succ h ih =>
    cases paths with
    | stop => simp [covered]
    | fork left right =>
      simp only [covered, Nat.pow_succ]
      have hl := ih left
      have hr := ih right
      omega

inductive Packet where
  | left (index : Nat)
  | right (index : Nat)
  deriving DecidableEq

def readOrigin (q u t : Nat) : Packet :=
  if t < u then .right t
  else if t < u + q then .left (t - u)
  else .right (t - q)

theorem left_destination (q u i : Nat) (bound : i < q) :
    readOrigin q u (u + i) = .left i := by
  have lower : ¬ u + i < u := by omega
  have upper : u + i < u + q := by omega
  simp [readOrigin, lower, upper]
  omega

theorem right_destination (q u j : Nat) :
    readOrigin q u (if j < u then j else q + j) = .right j := by
  by_cases low : j < u
  · simp [low, readOrigin]
  · have h1 : ¬ q + j < u := by omega
    have h2 : ¬ q + j < u + q := by omega
    simp [readOrigin, low, h1, h2]
    omega

theorem offsets_give_distinct_ports (i u v : Nat) (different : u ≠ v) :
    2 * (u + i) ≠ 2 * (v + i) := by omega

end OffsetPacketRoutes
