import Std

namespace AdaptiveCrossedCommunication

/-- The public successor action and the data-dependent chosen offset. -/
def link (A : Nat → α → α) (d : Nat) (e : α × α) : α × α := (e.2, A d e.1)

def chain (A : Nat → α → α) : List Nat → α × α → α × α
  | [], e => e
  | d :: ds, e => chain A ds (link A d e)

theorem two_links (A : Nat → α → α) (a b : Nat) (e : α × α) :
    link A b (link A a e) = (A a e.1, A b e.2) := rfl

/-- A root memory value remains an endpoint, with transport charged at most
    once for each pair of links and once for an unmatched link. -/
theorem root_endpoint (A : Nat → α → α) (zero : ∀ x, A 0 x = x)
    (add : ∀ a b x, A (a+b) x = A a (A b x)) (r : Nat)
    (ds : List Nat) (small : ∀ d ∈ ds, d ≤ r) (e : α × α) :
    ∃ s, s ≤ ((ds.length+1)/2)*r ∧
      (A s e.2 = (chain A ds e).1 ∨ A s e.2 = (chain A ds e).2) := by
  match ds with
  | [] => exact ⟨0, Nat.zero_le _, Or.inr (zero _)⟩
  | [d] => exact ⟨0, Nat.zero_le _, Or.inl (zero _)⟩
  | a :: b :: rest =>
    obtain ⟨s, hs, he⟩ := root_endpoint A zero add r rest
      (fun d hd => small d (by simp [hd])) (link A b (link A a e))
    have hb := small b (by simp)
    refine ⟨s+b, ?_, ?_⟩
    · simp only [List.length_cons]
      have len : (rest.length+1+1+1)/2 = (rest.length+1)/2+1 := by omega
      rw [len, Nat.add_mul, Nat.one_mul]
      omega
    · rw [add]
      exact he
termination_by ds.length

/-- The short group's ending displacement is represented by d₂−(v−j). -/
theorem short_group (u j v L d₁ d₂ r : Nat) (h₁ : u < j) (h₂ : j < v)
    (short : v-u < L) (congruence : (v-u)%L = d₁%L) (b₁ : d₁ ≤ r)
    (b₂ : d₂ ≤ r) :
    -(r : Int) ≤ (d₂ : Int) - ((v : Int)-j) ∧
    (d₂ : Int) - ((v : Int)-j) ≤ r := by
  rw [Nat.mod_eq_of_lt short] at congruence
  have residue := Nat.mod_le d₁ L
  omega

def drift (z : Int) (ds : List (Nat × Nat)) : Int :=
  match ds with
  | [] => z
  | (a,b) :: rest => drift (z+(b:Int)-a) rest

/-- After the last short group, signed displacement increases by at most r
    per remaining group, including groups wrapping the circle. -/
theorem transported_displacement (r : Nat) (ds : List (Nat × Nat))
    (small : ∀ d ∈ ds, d.1 ≤ r ∧ d.2 ≤ r) (z B : Int)
    (hz : -B ≤ z ∧ z ≤ B) :
    -(B+(ds.length : Int)*r) ≤ drift z ds ∧ drift z ds ≤ B+(ds.length : Int)*r := by
  induction ds generalizing B z with
  | nil => simpa [drift] using hz
  | cons hd rest ih =>
    obtain ⟨a,b⟩ := hd
    have head := small (a,b) (by simp)
    have ha : a ≤ r := head.1
    have hb : b ≤ r := head.2
    have hrest := ih (fun d hd => small d (by simp [hd])) (z+(b:Int)-a) (B+r)
      (by omega)
    simp only [drift, List.length_cons, Int.natCast_add,
      Int.natCast_one, Int.add_mul, Int.one_mul]
    omega

/-- Disjoint long groups fit in at most P−1 full revolutions. -/
theorem long_count (count L m P : Nat) (covered : count*L ≤ m-1)
    (upper : m-1 < P*L) : count < P :=
  Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt covered upper)

end AdaptiveCrossedCommunication
