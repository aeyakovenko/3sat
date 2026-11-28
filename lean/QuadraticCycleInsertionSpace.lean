import Std

namespace QuadraticCycleInsertionSpace

/-- Independence along the ordinary path starting at the given first bit. -/
def pathFrom (first : Bool) : List Bool → Bool
  | [] => true
  | next :: rest => !(first && next) && pathFrom next rest

private theorem last_edge (b c d : Bool) (middle : List Bool) :
    pathFrom b (middle ++ [c,d]) = (pathFrom b (middle ++ [c]) && !(c && d)) := by
  induction middle generalizing b with
  | nil => simp [pathFrom]
  | cons z rest ih => simp [pathFrom, ih, Bool.and_assoc]

/-- The four vertices 0, 1, n-2 and n-1 of the target graph span a clique. -/
def cliqueIndependent (a b c d : Bool) : Bool :=
  !((a && b) || (a && c) || (a && d) || (b && c) || (b && d) || (c && d))

/-- An endpoint replaces its own independent-set bit by one plus that bit
plus the neighboring bit, over GF(2). The neighbors stay fixed. -/
def endpoint (a b : Bool) : Bool := !(a ^^ b)

theorem endpoint_involution (a b : Bool) : endpoint (endpoint a b) b = a := by
  cases a <;> cases b <;> decide

/-- For an arbitrary length 4 + middle.length, the independent sets of the
source path containing an endpoint are conjugate to the independent sets of
K4 on the four displayed sites together with the unchanged path b,...,c.
The inverse is exactly the same coordinate change by endpoint_involution. -/
theorem conjugacy (a b c d : Bool) (middle : List Bool) :
    (pathFrom a (b :: (middle ++ [c,d])) && (a || d)) =
    (pathFrom b (middle ++ [c]) &&
      cliqueIndependent (endpoint a b) b c (endpoint d c)) := by
  rw [pathFrom, last_edge]
  generalize pathFrom b (middle ++ [c]) = p
  cases a <;> cases b <;> cases c <;> cases d <;> cases p <;> decide

/-- Evaluate a square-free polynomial in characteristic two at the set r.
Every proper subset is numerically smaller than r. The coefficient of r is
written separately from the parity of the nonzero proper-subset coefficients. -/
def polynomialValue (coefficient : Nat → Bool) (r : Nat) : Bool :=
  coefficient r ^^
    (((List.range r).filter (fun m => ((m &&& r) == m) && coefficient m)).length % 2 == 1)

private theorem value_when_lower_zero {coefficient : Nat → Bool} {r : Nat}
    (h : ∀ m, m < r → m &&& r = m → coefficient m = false) :
    polynomialValue coefficient r = coefficient r := by
  have he : (List.range r).filter (fun m => ((m &&& r) == m) && coefficient m) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro m hm
    by_cases hs : m &&& r = m
    · simp [hs, h m (List.mem_range.mp hm) hs]
    · simp [hs]
  simp [polynomialValue, he]

/-- For any hereditary family, a polynomial vanishes throughout that family
exactly when its coefficient at every member is zero. For graph-independent
sets this says the vanishing polynomials are spanned by monomials containing
an edge. No degree bound or Gaussian-elimination implementation enters here. -/
theorem hereditary_kernel (allowed : Nat → Prop)
    (down : ∀ m r, m &&& r = m → allowed r → allowed m) (coefficient : Nat → Bool) :
    (∀ r, allowed r → polynomialValue coefficient r = false) ↔
    (∀ r, allowed r → coefficient r = false) := by
  constructor
  · intro vanishes r
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro hr
      have h := value_when_lower_zero (coefficient := coefficient) (r := r)
        (fun m hm hs => ih m hm (down m r hs hr))
      exact h.symm.trans (vanishes r hr)
  · intro zeros r hr
    rw [value_when_lower_zero (fun m _ hs => zeros m (down m r hs hr)), zeros r hr]

/-- Direct calculation in the *original* independent-set coordinates. Each
natural number is a subset of the n sites. Constant, all singletons, and all
unordered pairs index the square-free monomials in degree at most two. -/
def monomials (n : Nat) : List Nat :=
  [0] ++ (List.range n).map (fun i => 1 <<< i) ++
    (List.range n).flatMap (fun j => (List.range j).map (fun i => (1 <<< i) ||| (1 <<< j)))

def forced (n row : Nat) : Bool :=
  (row &&& (row >>> 1) == 0) && (row.testBit 0 || row.testBit (n-1))

def evaluationRow (ms : List Nat) (row : Nat) : Nat :=
  (ms.zipIdx).foldl (fun v m =>
    if row &&& m.1 == m.1 then v ||| (1 <<< m.2) else v) 0

/-- Gaussian insertion from high pivot to low; XOR is GF(2) row addition. -/
def addRow (basis : Array Nat) (r : Nat) : Nat → Array Nat
  | 0 => basis
  | j+1 =>
    if !r.testBit j then addRow basis r j
    else
      let pivot := basis[j]?.getD 0
      if pivot == 0 then basis.setIfInBounds j r
      else addRow basis (r ^^^ pivot) j

def profile (n : Nat) : Nat × Nat × Nat :=
  let ms := monomials n
  let rows := (List.range (2^n)).filter (forced n)
  let basis := rows.foldl (fun bs r => addRow bs (evaluationRow ms r) ms.length)
    (Array.replicate ms.length 0)
  let rank := (basis.toList.filter (· != 0)).length
  (ms.length, rank, ms.length-rank)

/-- Triples give the number of square-free monomials, the elimination rank,
and their difference. This calculation uses neither conjugacy nor the proposed
four extra kernel generators. -/
theorem direct_quadratic_profiles : ([5,6,7,8,9].map profile) =
    [(16,8,8),(22,13,9),(29,19,10),(37,26,11),(46,34,12)] := by native_decide

end QuadraticCycleInsertionSpace
