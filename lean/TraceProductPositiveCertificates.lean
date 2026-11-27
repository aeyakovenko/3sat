import Std

namespace TraceProductPositiveCertificates

/-- Dimension accounting for pulling back an alternating form from its
    symplectic quotient: h = dimension of the restricted space, s = dimension
    of its intersection with the line radical. -/
theorem restrictedRanks {m h s r : Nat} (hd : h = 2*m+2) (hs : s ≤ m)
    (rankBound : 2*h ≤ r + 2*s + 2*m) :
    4 ≤ r ∧ (s < m → 6 ≤ r) := by omega

/-- A constant restriction forces three independent scalar lines to supply
    too many dimensions on a flat of binary dimension 2m-1. -/
theorem threeLineContradiction {m h s₁ s₂ s₃ : Nat} (hm : 3 ≤ m)
    (hd : h+1 = 2*m) (a : 2*h ≤ 2*s₁+2*m)
    (b : 2*h ≤ 2*s₂+2*m) (c : 2*h ≤ 2*s₃+2*m)
    (directSum : s₁+s₂+s₃ ≤ h) : False := by omega

/-- On a K-plane two coordinates are jointly injective; one of their
    projections from a binary (2m-1)-flat must have full binary rank. -/
theorem surjectiveCoordinate {m h a b : Nat} (hd : h+1 = 2*m)
    (ha : a ≤ m) (hb : b ≤ m) (injective : h ≤ a+b) : a=m ∨ b=m := by omega

/-- Count form of the derivative estimate. H is the size of the flat, C the
    contained-line directions including zero, and S the absolute character sum. -/
theorem strictCorrelation {H C S : Nat} (room : 24 ≤ H) (rare : 4*C ≤ H)
    (energy : 8*(S*S) ≤ H*(H+C+6)) : 16*S < 7*H := by
  have small : 2*(H+C+6) ≤ 3*H := by omega
  have compressed : 16*(S*S) ≤ 3*(H*H) := calc
    16*(S*S) = 2*(8*(S*S)) := by change (2*8)*(S*S) = _; ac_rfl
    _ ≤ 2*(H*(H+C+6)) := Nat.mul_le_mul_left 2 energy
    _ = H*(2*(H+C+6)) := by ac_rfl
    _ ≤ H*(3*H) := Nat.mul_le_mul_left H small
    _ = 3*(H*H) := by ac_rfl
  by_cases good : 16*S < 7*H
  · exact good
  · have bad : 7*H ≤ 16*S := by omega
    have lower : 49*(H*H) ≤ 256*(S*S) := calc
      49*(H*H) = (7*H)*(7*H) := by change (7*7)*(H*H) = _; ac_rfl
      _ ≤ (16*S)*(16*S) := Nat.mul_le_mul bad bad
      _ = 256*(S*S) := by change _ = (16*16)*(S*S); ac_rfl
    have pos : 0 < H*H := Nat.mul_pos (by omega) (by omega)
    omega

private def sign (b : Bool) : Int := if b then -1 else 1

/-- On a positive certificate, modulating by its indicator raises the signed
    sum by twice the number of certified points. -/
theorem signedDifference {α : Type} (points : List α) (f q : α → Bool)
    (cover : ∀ x ∈ points, q x = true → f x = true) :
    (points.map (fun x => sign (f x) * sign (q x))).sum -
      (points.map (fun x => sign (f x))).sum =
      2 * ((points.filter q).length : Int) := by
  induction points with
  | nil => simp
  | cons x xs ih =>
    have tail := ih (fun y hy => cover y (List.mem_cons_of_mem _ hy))
    cases v : q x with
    | false => simp [v, sign, List.sum_cons] at tail ⊢; omega
    | true =>
      have t := cover x (by simp) v
      simp [v, t, sign, List.sum_cons] at tail ⊢
      omega

theorem certificateContradiction {H A original modulated : Int}
    (large : 7*H ≤ 16*A)
    (lower : -(7*H) < 16*original) (upper : 16*modulated < 7*H)
    (diff : modulated - original = 2*A) : False := by omega

/-- The seventh-neighbor test used on the erased intersection of two flats.
A quadratic on a three-cube has the seven displayed coefficient bits. -/
private def q3 (d a b c e f g x y z : Bool) : Bool :=
  d ^^ (a && x) ^^ (b && y) ^^ (c && z) ^^ (e && x && y) ^^
    (f && x && z) ^^ (g && y && z)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem quadraticEighthCorner :
    ∀ d a b c e f g : Bool,
      let q := q3 d a b c e f g
      (∀ x y z : Bool, (x && y && z) = false → q x y z = true) →
      q true true true = true := by decide

/-- Every equation accepting a punctured three-cube accepts its final point. -/
theorem quadraticFamilyEighthCorner {I : Type} (row : I → Bool → Bool → Bool → Bool)
    (repr : ∀ i, ∃ d a b c e f g, row i = q3 d a b c e f g)
    (punctured : ∀ x y z : Bool, (x && y && z) = false →
      ∀ i, row i x y z = true) :
    ∀ i, row i true true true = true := by
  intro i
  obtain ⟨d, a, b, c, e, f, g, h⟩ := repr i
  rw [h]
  exact quadraticEighthCorner d a b c e f g (fun x y z corner => by
    simpa [← h] using punctured x y z corner i)

end TraceProductPositiveCertificates
