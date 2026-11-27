import Std

namespace FirstGeneratedNativeAddresses

/-- First effective edits consumed at a new scalar's birth and at later chosen
    first generators of previously unavailable numeric input addresses. -/
structure Scalar where
  own : Nat
  later : Nat

def Scalar.total (s : Scalar) := s.own + s.later

/-- A nonexceptional scalar either fits one two-charge slot or is grouped
    with one different reserved slot. -/
inductive Booking : List Scalar → Prop where
  | empty : Booking []
  | one {x xs} (small : x.total ≤ 2) (tail : Booking xs) : Booking (x :: xs)
  | two {x r xs} (high : x.own ≤ 1 ∧ x.later ≤ 2)
      (reserve : r.own ≤ 1 ∧ r.later = 0) (tail : Booking xs) : Booking (x :: r :: xs)

theorem booked_sum (xs : List Scalar) (h : Booking xs) :
    (xs.map Scalar.total).sum ≤ 2*xs.length := by
  induction h with
  | empty => decide
  | one small _ ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega
  | two high reserve _ ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    unfold Scalar.total at *
    obtain ⟨h₁,h₂⟩ := high
    obtain ⟨h₃,h₄⟩ := reserve
    omega

/-- The final fixed-program, scoped error form of the 5/2 theorem.
    xs is the list of new outside scalars in a pairing order, spare the other
    surplus slots, init the number of preavailable marked-address values. -/
theorem five_halves (m g E T init sparse spare : Nat) (xs : List Scalar)
    (booked : Booking xs) (count : m ≤ 2*spare + (xs.map Scalar.total).sum + sparse)
    (parts : E = spare + xs.length) (generated : m ≤ g + init)
    (clock : T = m+g+E) :
    5*m ≤ 2*T + sparse + 2*init := by
  have used := booked_sum xs booked
  omega

/-- For the promised one-bit alternatives, at most two generic addresses per
    outside partner give the weaker three-for-one surplus inequality. -/
theorem seven_thirds (m g h E T init sparse : Nat)
    (charged : m+h ≤ 2*E+2*h+sparse) (new_outside : h ≤ E)
    (generated : m ≤ g+init) (clock : T=m+g+E) :
    7*m ≤ 3*T+sparse+3*init := by omega

end FirstGeneratedNativeAddresses
