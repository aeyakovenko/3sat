import Std

/-! Uniqueness of two pieces of the local certificate: longest common
prefix lengths (direct position challenges) and first-occurrence pointers. -/
namespace CanonicalLongNames

structure Spelling where
  len : Nat
  digit : Nat → Nat

structure CheckedPrefix (u v : Spelling) (l : Nat) : Prop where
  leftBound : l ≤ u.len
  rightBound : l ≤ v.len
  agreement : ∀ j, j < l → u.digit j = v.digit j
  stopped : l = u.len ∨ l = v.len ∨ u.digit l ≠ v.digit l

theorem prefix_cannot_be_shorter {u v : Spelling} {l k : Nat}
    (hl : CheckedPrefix u v l) (hk : CheckedPrefix u v k) : ¬ l < k := by
  intro shorter
  rcases hl.stopped with ending | ending | disagree
  · have := hk.leftBound
    omega
  · have := hk.rightBound
    omega
  · exact disagree (hk.agreement l shorter)

theorem unique_prefix {u v : Spelling} {l k : Nat}
    (hl : CheckedPrefix u v l) (hk : CheckedPrefix u v k) : l = k := by
  have := prefix_cannot_be_shorter hl hk
  have := prefix_cannot_be_shorter hk hl
  omega

theorem checked_prefix_exists (u v : Spelling) : ∃ l, CheckedPrefix u v l := by
  have prefixCases : ∀ n, n ≤ u.len → n ≤ v.len →
      (∃ l, CheckedPrefix u v l) ∨ (∀ j, j < n → u.digit j = v.digit j) := by
    intro n
    induction n with
    | zero => intro _ _; exact Or.inr (by omega)
    | succ n ih =>
        intro hu hv
        obtain done | prev := ih (by omega) (by omega)
        · exact Or.inl done
        · by_cases equal : u.digit n = v.digit n
          · right
            intro j hj
            by_cases below : j < n
            · exact prev j below
            · have : j = n := by omega
              simpa [this] using equal
          · exact Or.inl ⟨n, ⟨by omega, by omega, prev, Or.inr (Or.inr equal)⟩⟩
  let n := min u.len v.len
  obtain done | agree := prefixCases n (Nat.min_le_left ..) (Nat.min_le_right ..)
  · exact done
  · refine ⟨n, ⟨Nat.min_le_left .., Nat.min_le_right .., agree, ?_⟩⟩
    by_cases order : u.len ≤ v.len
    · exact Or.inl (Nat.min_eq_left order)
    · exact Or.inr (Or.inl (Nat.min_eq_right (by omega)))

def FirstPointer (occurs : Nat → Prop) (pointer : Option Nat) : Prop :=
  match pointer with
  | none => ∀ i, ¬ occurs i
  | some k => occurs k ∧ ∀ i, occurs i → k ≤ i

theorem unique_first {occurs : Nat → Prop} {p q : Option Nat}
    (hp : FirstPointer occurs p) (hq : FirstPointer occurs q) : p = q := by
  cases p with
  | none =>
      cases q with
      | none => rfl
      | some j => exact False.elim (hp j hq.1)
  | some i =>
      cases q with
      | none => exact False.elim (hq i hp.1)
      | some j =>
        exact congrArg some (Nat.le_antisymm (hp.2 j hq.1) (hq.2 i hp.1))

#print axioms unique_prefix
#print axioms checked_prefix_exists
#print axioms unique_first

end CanonicalLongNames
