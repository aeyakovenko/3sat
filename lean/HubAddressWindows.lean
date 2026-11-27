import Std

namespace HubAddressWindows

variable {Addr Word : Type} [DecidableEq Addr]

def write (mem : Addr → Word) (a : Addr) (v : Word) (q : Addr) : Word :=
  if q=a then v else mem q

/-- A read/overwrite pair is a no-op on every address, including the selected hub. -/
theorem same_value (mem : Addr → Word) (a q : Addr) : write mem a (mem a) q = mem q := by
  by_cases equal : q=a
  · subst q; simp [write]
  · simp [write,equal]

/-- If two nonhub references lie in different selected ticks, even the last
reference of the earlier pair is too far from the first of the next pair. -/
theorem reference_gap (period radius i j a b : Nat) (space : radius+2 ≤ period)
    (before : i<j) (second : a≤1) : period*i+a+radius < period*j+b := by
  have h := Nat.mul_le_mul_left period (Nat.succ_le_of_lt before)
  rw [Nat.mul_succ] at h
  omega

/-- The selected pair in each tick carries a single address. Windows may start
or end between a read and its matching write. -/
theorem short_window (period radius lo hi i j a b offset : Nat)
    (value : Nat → Addr) (space : radius+2 ≤ period)
    (fa : a≤1) (fb : b≤1) (left : lo=period*i+offset+a)
    (right : hi=period*j+offset+b) (order : lo≤hi) (window : hi≤lo+radius) :
    value i = value j := by
  by_cases same : i=j
  · rw [same]
  · rcases Nat.lt_or_gt_of_ne same with less|more
    · have gap := reference_gap period radius i j a b space less fa
      omega
    · have gap := reference_gap period radius j i b a space more fb
      omega

end HubAddressWindows

#print axioms HubAddressWindows.same_value
#print axioms HubAddressWindows.short_window
