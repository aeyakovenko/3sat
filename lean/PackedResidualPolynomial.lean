import Std

namespace PackedResidualPolynomial

inductive Tree (var : Type) where
  | leaf (answer : Bool)
  | node (key : var) (low high : Tree var)

def Tree.eval (setting : var → Bool) : Tree var → Bool
  | .leaf a => a
  | .node v l h => if setting v then h.eval setting else l.eval setting

inductive Polynomial (var : Type) where
  | constant (a : Bool)
  | variable (v : var)
  | plus (p q : Polynomial var)
  | times (p q : Polynomial var)

def Polynomial.eval (setting : var → Bool) : Polynomial var → Bool
  | .constant a => a
  | .variable v => setting v
  | .plus p q => xor (p.eval setting) (q.eval setting)
  | .times p q => (p.eval setting) && (q.eval setting)

def Tree.height : Tree var → Nat
  | .leaf _ => 0
  | .node _ l h => 1 + max l.height h.height

def Polynomial.degreeBound : Polynomial var → Nat
  | .constant _ => 0
  | .variable _ => 1
  | .plus p q => max p.degreeBound q.degreeBound
  | .times p q => p.degreeBound + q.degreeBound

def Tree.toPolynomial : Tree var → Polynomial var
  | .leaf a => .constant a
  | .node v l h => .plus l.toPolynomial
      (.times (.variable v) (.plus l.toPolynomial h.toPolynomial))

theorem conversion_exact (t : Tree var) (s : var → Bool) :
    t.toPolynomial.eval s = t.eval s := by
  induction t with
  | leaf _ => rfl
  | node v l h ihl ihh =>
    simp only [Tree.toPolynomial, Polynomial.eval, Tree.eval, ihl, ihh]
    cases s v <;> cases l.eval s <;> cases h.eval s <;> rfl

theorem conversion_degree (t : Tree var) :
    t.toPolynomial.degreeBound ≤ t.height := by
  induction t with
  | leaf _ => exact Nat.le_refl _
  | node v l h ihl ihh =>
    simp only [Tree.toPolynomial, Polynomial.degreeBound, Tree.height]
    omega

/-- Residual coefficient trees in descending variable order. The left
subtree omits that variable and the right subtree is its coefficient. -/
inductive Coeff (lane : Type) : Nat → Type where
  | word (v : lane → Bool) : Coeff lane 0
  | split (lo hi : Coeff lane n) : Coeff lane (n+1)

def Coeff.add : {n : Nat} → Coeff lane n → Coeff lane n → Coeff lane n
  | 0, .word p, .word q => .word (fun i => xor (p i) (q i))
  | _+1, .split a b, .split c d => .split (a.add c) (b.add d)

def Bits : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Bits n

def Coeff.eval : {n : Nat} → Coeff lane n → Bits n → lane → Bool
  | 0, .word p, _, i => p i
  | _+1, .split a b, (x, xs), i => xor (a.eval xs i) (x && b.eval xs i)

theorem add_eval : {n : Nat} → (a b : Coeff lane n) → (x : Bits n) → (i : lane) →
    (a.add b).eval x i = xor (a.eval x i) (b.eval x i)
  | 0, .word _, .word _, _, _ => rfl
  | _+1, .split a b, .split c d, (x, xs), i => by
    simp only [Coeff.add, Coeff.eval, add_eval a c xs i, add_eval b d xs i]
    cases x <;> cases a.eval xs i <;> cases b.eval xs i <;>
      cases c.eval xs i <;> cases d.eval xs i <;> rfl

def descend : {n : Nat} → Coeff lane n → Bits n → lane → Bool
  | 0, .word p, _ => p
  | _+1, .split a b, (x,xs) => descend (if x then a.add b else a) xs

theorem descend_exact : {n : Nat} → (p : Coeff lane n) → (x : Bits n) → (i : lane) →
    descend p x i = p.eval x i
  | 0, .word _, _, _ => rfl
  | _+1, .split a b, (x,xs), i => by
    cases x <;> simp [descend, descend_exact a xs i,
      descend_exact (a.add b) xs i, Coeff.eval, add_eval]

#print axioms conversion_degree
#print axioms descend_exact

end PackedResidualPolynomial
