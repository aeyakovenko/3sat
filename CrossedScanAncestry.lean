import Std

namespace CrossedScanAncestry

/-- A write stores either the current public address or its successor. -/
def shift (S : α → α) (offset : Bool) (a : α) : α := if offset then S a else a

def link (S : α → α) (offset : Bool) (e : α × α) : α × α :=
  (e.2, shift S offset e.1)

def chain (S : α → α) : List Bool → α × α → α × α
  | [], e => e
  | d :: ds, e => chain S ds (link S d e)

def advance (S : α → α) : Nat → α → α
  | 0, a => a
  | n+1, a => advance S n (S a)

theorem two_links (S : α → α) (d₁ d₂ : Bool) (e : α × α) :
    link S d₂ (link S d₁ e) = (shift S d₁ e.1, shift S d₂ e.2) := rfl

/-- The original memory value still occurs at one endpoint, advanced at most once
    per two provenance links, plus one for an odd final link. -/
theorem root_endpoint (S : α → α) (ds : List Bool) (e : α × α) :
    ∃ j, j ≤ (ds.length+1)/2 ∧
     (advance S j e.2 = (chain S ds e).1 ∨ advance S j e.2 = (chain S ds e).2) := by
  match ds with
  | [] => exact ⟨0, Nat.zero_le _, Or.inr rfl⟩
  | [a] => exact ⟨0, Nat.zero_le _, Or.inl rfl⟩
  | a::b::rest =>
    obtain ⟨j, bound, endpt⟩ := root_endpoint S rest (link S b (link S a e))
    simp only [List.length_cons]
    cases b with
    | false =>
      refine ⟨j, by omega, ?_⟩
      simpa [chain, link, shift] using endpt
    | true =>
      refine ⟨j+1, by omega, ?_⟩
      simpa [chain, link, shift, advance] using endpt
termination_by ds.length

/-- Two increasing event indices with a total of two provenance links consume a wrap.
    The modular identity comes from the first coordinate of two_links. -/
theorem two_link_cost (u v d L : Nat) (strictTimes : u+2 ≤ v) (small : d ≤ 1)
    (periodic : v % L = (u+d) % L) : u+d+L ≤ v := by
  have ha := Nat.mod_add_div (u+d) L
  have hb := Nat.mod_add_div v L
  have quot : (u+d)/L < v/L := by
    apply Nat.lt_of_not_ge
    intro bad
    have monotone := Nat.mul_le_mul_left L bad
    omega
  have full := Nat.mul_le_mul_left L quot
  rw [Nat.mul_succ] at full
  omega

theorem paired_span (time : Nat → Nat) (L : Nat)
    (gap : ∀ i, time i+L ≤ time (i+2)) (p : Nat) :
    time 0+p*L ≤ time (2*p) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have next := gap (2*p)
    rw [Nat.succ_mul, Nat.mul_succ]
    omega

/-- If the whole run fits in P passes and each pair costs a pass, root transport
    uses at most P steps of S. The premise uses a strict end index, even at a wrap. -/
theorem ceil_links_le_passes (t L P : Nat) (span : (t/2)*L < P*L) :
    (t+1)/2 ≤ P := by
  have fewer : t/2 < P := Nat.lt_of_mul_lt_mul_right span
  omega

theorem destination_bound (changed inside h passes : Nat)
    (charge : changed ≤ inside + passes*inside + 1)
    (orbitUnion : inside ≤ (passes+1)*h) :
    changed ≤ (passes+1)^2*h + 1 := by
  have foldCount : inside + passes*inside = (passes+1)*inside := by
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  rw [foldCount] at charge
  have mono := Nat.mul_le_mul_left (passes+1) orbitUnion
  rw [Nat.pow_two, Nat.mul_assoc]
  omega

end CrossedScanAncestry
