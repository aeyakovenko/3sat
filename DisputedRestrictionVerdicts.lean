import Std

namespace DisputedRestrictionVerdicts

/-- In the hard game, an adviser query gets one bit depending on the hidden
    point. A direct check gets its genuine membership bit. Children are in
    false/true order. -/
inductive Protocol (A : Type) where
  | halt (verdict : Bool)
  | ask (reply : A → Bool) (no yes : Protocol A)
  | check (point : A) (no yes : Protocol A)

def run {A : Type} (hidden : A) (member : A → Bool) : Protocol A → Bool
  | .halt verdict => verdict
  | .ask reply no yes =>
    if reply hidden then run hidden member yes else run hidden member no
  | .check point no yes =>
    if member point then run hidden member yes else run hidden member no

/-- A list covering the assignment checks in all transcripts that have had
    only negative direct replies. Shared prefixes need only be listed once. -/
def exposed {A : Type} : Protocol A → List A
  | .halt _ => []
  | .ask _ no yes => exposed no ++ exposed yes
  | .check point no _ => point :: exposed no

theorem agree_if_unexposed {A : Type} [DecidableEq A] (p : Protocol A) (u : A)
    (miss : u ∉ exposed p) :
    run u (fun x => decide (u = x)) p = run u (fun _ => false) p := by
  induction p with
  | halt => rfl
  | ask reply no yes ihn ihy =>
    simp only [exposed, List.mem_append, not_or] at miss
    cases h : reply u <;> simp [run, h, ihn miss.1, ihy miss.2]
  | check x no yes ihn _ =>
    simp only [exposed, List.mem_cons, not_or] at miss
    simp [run, miss.1, ihn miss.2]

/-- Only the paths with negative direct replies are needed for the bound. -/
inductive Budget {A : Type} : Protocol A → Nat → Nat → Prop where
  | halt (v : Bool) (q b : Nat) : Budget (.halt v) q b
  | ask {no yes : Protocol A} {q b : Nat} (reply : A → Bool) :
    Budget no q b → Budget yes q b → Budget (.ask reply no yes) (q+1) b
  | check {no : Protocol A} {q b : Nat} (x : A) (yes : Protocol A) :
    Budget no q b → Budget (.check x no yes) q (b+1)

theorem exposed_bound {A : Type} {p : Protocol A} {q b : Nat}
    (h : Budget p q b) : (exposed p).length ≤ b * 2^q := by
  induction h with
  | halt => simp [exposed]
  | @ask no yes q b _ _ _ ih₀ ih₁ =>
    simp only [exposed, List.length_append, Nat.pow_succ, ← Nat.mul_assoc]
    omega
  | @check no q b x _ _ ih =>
    simp only [exposed, List.length_cons, Nat.add_mul, Nat.one_mul]
    have hpos := Nat.two_pow_pos q
    omega

/-- Exact distinction forces a short covering list for every possible
    singleton. In particular a universe of distinct points has size at most
    the length of this list. -/
theorem covering_list {A : Type} [DecidableEq A]
    {p : Protocol A} {q b : Nat} (h : Budget p q b) (domain : List A)
    (different : ∀ u ∈ domain,
      run u (fun x => decide (u = x)) p ≠ run u (fun _ => false) p) :
    ∃ points : List A, points.length ≤ b * 2^q ∧ ∀ u ∈ domain, u ∈ points := by
  refine ⟨exposed p, exposed_bound h, ?_⟩
  intro u hu
  by_cases inside : u ∈ exposed p
  · exact inside
  · exact False.elim (different u hu (agree_if_unexposed p u inside))

end DisputedRestrictionVerdicts
