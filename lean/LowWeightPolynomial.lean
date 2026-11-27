import Std

namespace LowWeightPolynomial

/-- An assignment to exactly n Boolean variables, in their given order. -/
inductive Bits : Nat → Type
  | nil : Bits 0
  | cons {n : Nat} : Bool → Bits n → Bits (n+1)

def Bits.zeros : (n : Nat) → Bits n
  | 0 => .nil
  | n+1 => .cons false (zeros n)

def Bits.weight : {n : Nat} → Bits n → Nat
  | _, .nil => 0
  | _, .cons b x => (if b then 1 else 0) + x.weight

@[simp] theorem zerosWeight (n : Nat) : (Bits.zeros n).weight = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Bits.zeros, Bits.weight] using ih

/-- The two terms of a split use only the remaining variables. The node
    denotes p + x*q, so their monomial supports are disjoint. -/
inductive Poly (α : Type) : Nat → Type
  | const {n : Nat} : α → Poly α n
  | skip {n : Nat} : Poly α n → Poly α (n+1)
  | split {n : Nat} : Poly α n → Poly α n → Poly α (n+1)

variable {α : Type}

def eval (add : α → α → α) : {n : Nat} → Poly α n → Bits n → α
  | _, .const c, _ => c
  | _, .skip p, .cons _ x => eval add p x
  | _, .split p q, .cons b x => if b then add (eval add p x) (eval add q x) else eval add p x

/-- A monomial of degree k has a nonzero coefficient. Recording the
    degree this way ignores redundant zero branches in the syntax. -/
inductive Term (zero : α) : {n : Nat} → Poly α n → Nat → Prop
  | const {n : Nat} {c : α} : c ≠ zero → Term zero (.const (n := n) c) 0
  | skip {n k : Nat} {p : Poly α n} : Term zero p k → Term zero (.skip p) k
  | left {n k : Nat} {p q : Poly α n} : Term zero p k → Term zero (.split p q) k
  | right {n k : Nat} {p q : Poly α n} : Term zero q k → Term zero (.split p q) (k+1)

def DegreeLE (zero : α) {n : Nat} (p : Poly α n) (d : Nat) : Prop :=
  ∀ k, Term zero p k → k ≤ d

/-- If all coefficients are zero, every Boolean evaluation vanishes. -/
theorem evalZero (zero : α) (add : α → α → α) (zeroAdd : ∀ c, add zero c = c)
    {n : Nat} (p : Poly α n) (none : ∀ k, ¬ Term zero p k) (x : Bits n) :
    eval add p x = zero := by
  induction p with
  | const c =>
    apply Classical.byContradiction
    intro nz
    exact none 0 (.const nz)
  | skip p ih =>
    cases x with
    | cons b x => exact ih (fun k t => none k (.skip t)) x
  | split p q ip iq =>
    cases x with
    | cons b x =>
      have hp := ip (fun k t => none k (.left t)) x
      have hq := iq (fun k t => none (k+1) (.right t)) x
      cases b <;> simp [eval, hp, hq, zeroAdd]

/-- The witnessing evaluation can be chosen with weight bounded by the
    degree of an actual nonzero monomial. Only a left identity is used. -/
theorem witnessOfTerm (zero : α) (add : α → α → α) (zeroAdd : ∀ c, add zero c = c)
    {n : Nat} (p : Poly α n) (nonzero : ∃ k, Term zero p k) :
    ∃ k, Term zero p k ∧ ∃ x : Bits n, x.weight ≤ k ∧ eval add p x ≠ zero := by
  induction p with
  | @const n c =>
    obtain ⟨k, t⟩ := nonzero
    cases t with
    | const nz => exact ⟨0, .const nz, .zeros n, by simp, nz⟩
  | skip p ih =>
    obtain ⟨k, t⟩ := nonzero
    cases t with
    | skip tp =>
      obtain ⟨j, term, x, weight, nz⟩ := ih ⟨k, tp⟩
      exact ⟨j, .skip term, .cons false x, by simpa [Bits.weight] using weight, nz⟩
  | split p q ip iq =>
    by_cases left : ∃ j, Term zero p j
    · obtain ⟨j, term, x, weight, nz⟩ := ip left
      exact ⟨j, .left term, .cons false x, by simpa [Bits.weight] using weight, nz⟩
    · have noLeft : ∀ j, ¬ Term zero p j := fun j term => left ⟨j, term⟩
      have right : ∃ k, Term zero q k := by
        obtain ⟨k, t⟩ := nonzero
        cases t with
        | left tp => exact (noLeft _ tp).elim
        | right tq => exact ⟨_, tq⟩
      obtain ⟨j, term, x, weight, nz⟩ := iq right
      have absent := evalZero zero add zeroAdd p noLeft x
      refine ⟨j+1, .right term, .cons true x, ?_, ?_⟩
      · simp only [Bits.weight, ↓reduceIte]
        omega
      · simpa [eval, absent, zeroAdd] using nz

/-- A nonzero multilinear polynomial of degree at most d has a nonzero
    Boolean evaluation at Hamming weight at most d. -/
theorem lowWeightOfNonzero (zero : α) (add : α → α → α) (zeroAdd : ∀ c, add zero c = c)
    {n d : Nat} (p : Poly α n) (bound : DegreeLE zero p d)
    (nonzero : ∃ k, Term zero p k) :
    ∃ x : Bits n, x.weight ≤ d ∧ eval add p x ≠ zero := by
  obtain ⟨k, tk, x, weight, nz⟩ := witnessOfTerm zero add zeroAdd p nonzero
  exact ⟨x, Nat.le_trans weight (bound k tk), nz⟩

/-- Semantic nonzeroness also suffices, without assuming a field. -/
theorem lowWeightOfEvaluation (zero : α) (add : α → α → α) (zeroAdd : ∀ c, add zero c = c)
    {n d : Nat} (p : Poly α n) (bound : DegreeLE zero p d)
    (nonzero : ∃ x, eval add p x ≠ zero) :
    ∃ x : Bits n, x.weight ≤ d ∧ eval add p x ≠ zero := by
  apply lowWeightOfNonzero zero add zeroAdd p bound
  apply Classical.byContradiction
  intro missing
  obtain ⟨x, hx⟩ := nonzero
  exact hx (evalZero zero add zeroAdd p (fun k tk => missing ⟨k, tk⟩) x)

/-- A nonzero evaluation supported above a Hamming-weight threshold
    forces every degree bound to lie strictly above that threshold. -/
theorem supportedAbove (zero : α) (add : α → α → α) (zeroAdd : ∀ c, add zero c = c)
    {n d threshold : Nat} (p : Poly α n) (bound : DegreeLE zero p d)
    (nonzero : ∃ x, eval add p x ≠ zero)
    (support : ∀ x, eval add p x ≠ zero → threshold < x.weight) :
    threshold + 1 ≤ d := by
  obtain ⟨x, weight, nz⟩ := lowWeightOfEvaluation zero add zeroAdd p bound nonzero
  have above := support x nz
  omega

theorem strictMajorityDegree (zero : α) (add : α → α → α) (zeroAdd : ∀ c, add zero c = c)
    {n d : Nat} (p : Poly α n) (bound : DegreeLE zero p d)
    (nonzero : ∃ x, eval add p x ≠ zero)
    (majority : ∀ x, eval add p x ≠ zero → n < 2 * x.weight) :
    n / 2 + 1 ≤ d := by
  apply supportedAbove zero add zeroAdd p bound nonzero
  intro x hx
  have above := majority x hx
  omega

end LowWeightPolynomial
