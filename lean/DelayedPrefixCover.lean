import Std

namespace DelayedPrefixCover

/-- A fixed-width dispatch prefix chooses how many payload bits to consume.
    Distinct complete rows from this protocol are incomparable as prefixes. -/
theorem dispatched_rows_prefix_free {u v s t : List Bool}
    (payloadLength : List Bool → Nat) (headers : u.length = v.length)
    (hs : s.length = payloadLength u) (ht : t.length = payloadLength v)
    (isPrefix : List.IsPrefix (u ++ s) (v ++ t)) : u = v ∧ s = t := by
  obtain ⟨rest, h⟩ := isPrefix
  rw [List.append_assoc] at h
  obtain ⟨sameHeader, tailEq⟩ := List.append_inj h headers
  subst v
  have lenEq := congrArg List.length tailEq
  simp only [List.length_append] at lenEq
  have restLen : rest.length = 0 := by omega
  have restNil : rest = [] := List.length_eq_zero_iff.mp restLen
  simpa [restNil] using tailEq

/-- With header width j−1 and payload width m−j the exact name is
    one bit shorter than its j-zero-padded word. -/
theorem dispatch_lengths {j m : Nat} {header tail : List Bool}
    (jpos : 0 < j) (fits : j ≤ m) (hh : header.length = j-1)
    (ht : tail.length = m-j) :
    (header ++ tail).length + 1 = m ∧
      (List.replicate j false ++ tail).length = m := by
  simp only [List.length_append, List.length_replicate, hh, ht]
  omega

end DelayedPrefixCover
