import Mathlib.Tactic.Ring

/-! The Taylor divisibility and high-digit identity used in integer-polynomial gathers. -/
namespace IntegerPolynomialGather

def value : List ℤ → ℤ → ℤ
  | [], _ => 0
  | c :: cs, a => c + a * value cs a

def slope : List ℤ → ℤ → ℤ
  | [], _ => 0
  | _ :: cs, a => value cs a + a * slope cs a

theorem second_difference (cs : List ℤ) (a h : ℤ) :
    ∃ q : ℤ, value cs (a+h) = value cs a + h * slope cs a + h^2 * q := by
  induction cs with
  | nil => exact ⟨0, by simp [value, slope]⟩
  | cons c cs ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨slope cs a + (a+h)*q, ?_⟩
    simp only [value, slope]
    rw [hq]
    ring

theorem high_digit_congruence (cs : List ℤ) (a base u modulus : ℤ)
    (hdiv : modulus ∣ base^2) :
    modulus ∣ value cs (a+base*u) - (value cs a + base * (slope cs a*u)) := by
  obtain ⟨d, hd⟩ := hdiv
  obtain ⟨q, hq⟩ := second_difference cs a (base*u)
  use d * u^2 * q
  rw [hq]
  calc
    _ = base^2 * (u^2*q) := by ring
    _ = _ := by rw [hd]; ring

/-- Over binary fields, the translated quadratic term vanishes at h=b/a. -/
theorem cubic_translation {K : Type*} [CommRing K] (a h c d x : K) :
    a * (x + h)^3 - 3 * a * h * (x + h)^2 + c * (x + h) + d =
    a * x^3 + (c - 3*a*h^2)*x + (c*h - 2*a*h^3 + d) := by ring

theorem rescale_cubic {K : Type*} [CommRing K] (a g x : K) :
    a * (g*x)^3 + a * g^2 * (g*x) = a * g^3 * (x^3+x) := by ring

#print axioms high_digit_congruence
end IntegerPolynomialGather
