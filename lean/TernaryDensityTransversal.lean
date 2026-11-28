import Std

namespace TernaryDensityTransversal

/-- For a fixed assignment to the other variables, some positive occurrences
    may demand true and some negative occurrences may demand false. -/
def ways (positive negative : Bool) : Nat :=
  (!positive).toNat + (!negative).toNat

theorem aligning_one_variable : ∀ p n : Bool,
    ways p n ≤ ways (p || n) false := by decide +kernel

abbrev Family := List (List Nat)

def Hits (h : Family) (s : List Nat) : Prop :=
  ∀ e ∈ h, ∃ v, v ∈ e ∧ v ∈ s

def Needs (k : Nat) (h : Family) : Prop :=
  ∀ s, Hits h s → k ≤ s.length

/-- The bit on z is zero. All members of positive are set to one, so they are
    removed as candidates from the remaining edges. -/
def residual (h : Family) (z : Nat) (positive : List Nat) : Family :=
  (h.filter (fun e => !(e.contains z))).map fun e =>
    e.filter fun v => !(positive.contains v)

theorem lift_hits {h : Family} {z : Nat} {positive s : List Nat}
    (hit : Hits (residual h z positive) s) : Hits h (z :: s) := by
  intro e he
  by_cases hz : z ∈ e
  · exact ⟨z,hz,by simp⟩
  · have mem : e.filter (fun v => !(positive.contains v)) ∈ residual h z positive := by
      apply List.mem_map.mpr
      exact ⟨e, List.mem_filter.mpr ⟨he, by simpa using hz⟩, rfl⟩
    obtain ⟨v, hv, hs⟩ := hit _ mem
    exact ⟨v,(List.mem_filter.mp hv).1,by simp [hs]⟩

theorem residual_needs {h : Family} {k : Nat} (bound : Needs (k+1) h)
    (z : Nat) (positive : List Nat) : Needs k (residual h z positive) := by
  intro s hs
  have large := bound (z :: s) (lift_hits hs)
  simpa using large

/-- Integer numerator for surviving k rounds on a denominator of 8^k.
    An edge of one, two or three distinct vertices branches at the first zero.
    Its three possible branches consume respectively 4, 2 and 1 atoms out of 8.
    After a round unused fresh random bits are discarded. At the horizon all
    surviving states are provisionally accepted. The intended input consists
    of supports of size at most three. -/
def survival : Nat → Family → Nat
  | 0, _ => 1
  | k+1, [] => 8^(k+1)
  | _+1, [] :: _ => 0
  | k+1, [a] :: t =>
    4 * survival k (residual ([a] :: t) a [])
  | k+1, [a,b] :: t =>
    4 * survival k (residual ([a,b] :: t) a []) +
    2 * survival k (residual ([a,b] :: t) b [a])
  | k+1, (a :: b :: c :: u) :: t =>
    let h := (a :: b :: c :: u) :: t
    4 * survival k (residual h a []) +
    2 * survival k (residual h b [a]) +
        survival k (residual h c [a,b])

theorem survival_bound (k : Nat) (h : Family) (bound : Needs k h) :
    survival k h ≤ 7^k := by
  induction k generalizing h with
  | zero => simp [survival]
  | succ k ih =>
    have child (z : Nat) (positive : List Nat) :=
      ih (residual h z positive) (residual_needs bound z positive)
    rw [Nat.pow_succ]
    cases h with
    | nil =>
      have bad := bound [] (by intro e he; simp at he)
      simp at bad
    | cons e t =>
      cases e with
      | nil => simp [survival]
      | cons a e =>
        have ha := child a []
        cases e with
        | nil => simp only [survival]; omega
        | cons b e =>
          have hb := child b [a]
          cases e with
          | nil => simp only [survival]; omega
          | cons c u =>
            have hc := child c [a,b]
            simp only [survival]
            omega

end TernaryDensityTransversal
