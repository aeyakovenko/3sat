import Std

namespace RationalRangeSieve

/-- Enumerate sublists with inclusion decided once per source entry. -/
def selections : List α → List (List α)
  | [] => [[]]
  | a :: xs =>
    let rest := selections xs
    rest ++ rest.map (a :: ·)

/-- A selection contributes only when all its members witness the range query. -/
def signed (hit : α → Bool) : List α → Int
  | [] => 1
  | a :: xs => if hit a then -signed hit xs else 0

private theorem sumAppend (a b : List Int) : (a ++ b).sum = a.sum + b.sum := by
  induction a with
  | nil => simp
  | cons x xs ih => simp [ih, Int.add_assoc]

private theorem zeroTotal (a : List α) : (a.map (fun _ => (0:Int))).sum = 0 := by
  induction a with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem negTotal (a : List Int) : (a.map (fun x => -x)).sum = -a.sum := by
  induction a with
  | nil => simp
  | cons x xs ih => simp [ih, Int.neg_add]

/-- Complement-of-image membership is an exact signed sum, even when a
    queried value has arbitrarily many distinct source preimages. -/
theorem rangeSieve (hit : α → Bool) (xs : List α) :
    ((selections xs).map (signed hit)).sum = if xs.any hit then 0 else 1 := by
  induction xs with
  | nil => simp [selections, signed]
  | cons a xs ih =>
    simp only [selections, List.map_append, sumAppend, List.map_map,
      List.any_cons]
    by_cases h : hit a = true
    ·
      have neg := negTotal ((selections xs).map (signed hit))
      simp only [List.map_map, Function.comp_def] at neg
      simp [Function.comp_def, signed, h, neg] <;> omega
    · simpa [Function.comp_def, signed, h, zeroTotal] using ih

def Word : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Word n

def monomial : (n : Nat) → Word n → Word n → Int
  | 0, _, _ => 1
  | n+1, (m,ms), (x,xs) => if m && !x then 0 else monomial n ms xs

abbrev Term n := Word n × Int

/-- Terms before collecting equal monomials. Each occurrence has coefficient
    +1 or -1. The recursion is (1-x)*F(false)+x*F(true). -/
def terms : (n : Nat) → (Word n → Bool) → List (Term n)
  | 0, f => if f () then [((),1)] else []
  | n+1, f =>
    let lo := terms n (fun t => f (false,t))
    let hi := terms n (fun t => f (true,t))
    lo.map (fun (m,c) => ((false,m),c)) ++
      lo.map (fun (m,c) => ((true,m),-c)) ++
      hi.map (fun (m,c) => ((true,m),c))

theorem termCount (n : Nat) (f : Word n → Bool) : (terms n f).length ≤ 3^n := by
  induction n with
  | zero => cases h : f () <;> simp [terms, h]
  | succ n ih =>
    have lo := ih (fun t => f (false,t))
    have hi := ih (fun t => f (true,t))
    simp only [terms, List.length_append, List.length_map, Nat.pow_succ]
    omega

theorem coefficientUnit (n : Nat) (f : Word n → Bool) (t : Term n)
    (ht : t ∈ terms n f) : t.2 = 1 ∨ t.2 = -1 := by
  induction n with
  | zero =>
    cases h : f () <;> simp_all [terms]
  | succ n ih =>
    simp only [terms, List.mem_append, List.mem_map] at ht
    rcases ht with (⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩) | ⟨v,hv,rfl⟩
    · exact ih _ _ hv
    · have := ih _ _ hv
      change -v.2 = 1 ∨ -v.2 = -1
      omega
    · exact ih _ _ hv

def evaluate (n : Nat) (x : Word n) (t : Term n) : Int := t.2 * monomial n t.1 x

theorem booleanExpansion (n : Nat) (f : Word n → Bool) (x : Word n) :
    ((terms n f).map (evaluate n x)).sum = if f x then 1 else 0 := by
  induction n with
  | zero => cases x; cases h : f () <;> simp [terms, evaluate, monomial, h]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    have lo := ih (fun t => f (false,t)) x
    have hi := ih (fun t => f (true,t)) x
    have neg := negTotal ((terms n (fun t => f (false,t))).map (evaluate n x))
    simp only [List.map_map, Function.comp_def, evaluate] at lo hi neg
    change ((terms n _).map (fun t => t.2 * monomial n t.1 x)).sum = _ at lo hi
    change _ = -((terms n _).map (fun t => t.2 * monomial n t.1 x)).sum at neg
    cases b <;>
      simp [terms, evaluate, monomial, List.map_map, Function.comp_def, neg, lo, hi,
        Int.neg_mul, sumAppend, zeroTotal] <;> omega

end RationalRangeSieve
