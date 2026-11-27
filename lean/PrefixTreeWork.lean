import Std

namespace PrefixTreeWork

/-- One fixed timed/pruned computation: a unary node executes a fixed step,
and a binary node executes one fair-bit read. Leaves do no further work. -/
inductive Trace where
  | stop : Trace
  | step : Trace → Trace
  | read : Trace → Trace → Trace
  deriving Repr

def size : Trace → Nat
  | .stop => 0
  | .step t => 1 + size t
  | .read l r => 1 + size l + size r

def depth : Trace → Nat
  | .stop => 0
  | .step t => depth t
  | .read l r => max (depth l) (depth r) + 1

/-- Sum over every assignment to the remaining random bits. The current
weight doubles immediately after each read. The zero-budget read case is
unreachable when depth fits the supplied tape. -/
def tapeSum : Trace → Nat → Nat → Nat
  | .stop, _, _ => 0
  | .step t, n, w => 2 ^ n * w + tapeSum t n w
  | .read _ _, 0, _ => 0
  | .read l r, n + 1, w =>
    2 ^ (n + 1) * w + tapeSum l n (2 * w) + tapeSum r n (2 * w)

theorem exactWork (t : Trace) (n w : Nat) (enough : depth t ≤ n) :
    tapeSum t n w = 2 ^ n * w * size t := by
  induction t generalizing n w with
  | stop => simp [size, tapeSum]
  | step t ih =>
    simp [size, tapeSum, ih n w enough, Nat.mul_add]
  | read l r il ir =>
    cases n with
    | zero => simp [depth] at enough
    | succ n =>
      have hmax : max (depth l) (depth r) ≤ n := by simpa [depth] using enough
      have hl := Nat.le_trans (Nat.le_max_left _ _) hmax
      have hr := Nat.le_trans (Nat.le_max_right _ _) hmax
      simp [size, tapeSum, il n (2 * w) hl, ir n (2 * w) hr, Nat.pow_succ,
        Nat.mul_add, Nat.mul_assoc]

end PrefixTreeWork
