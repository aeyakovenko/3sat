import Std

namespace ResidualLineWitness

abbrev Pair := Bool × Bool

/-- The three nonempty subsets of a two-element set, named by a two-bit mask. -/
def masks : List Pair := [(true,false), (false,true), (true,true)]

def coefficient (u : Pair) : Int := if u.1 && u.2 then -1 else 1

structure Matrix where
  first : Pair
  second : Pair
  deriving DecidableEq, Repr

def restrictBy (b : Bool) (v : Pair) : Pair := (b && v.1, b && v.2)

def outer (u v : Pair) : Matrix := ⟨restrictBy u.1 v, restrictBy u.2 v⟩

def emptyMatrix : Matrix := ⟨(false,false), (false,false)⟩

/-- δ₀ plus the nine rank-one outer products with coefficients −a(U)a(V). -/
def squareMeasure : List (Matrix × Int) :=
  (emptyMatrix, 1) :: masks.flatMap fun u =>
    masks.map fun v => (outer u v, -(coefficient u * coefficient v))

theorem distinct_support : (squareMeasure.map Prod.fst).Nodup := by decide

def readLine (m : Matrix) (line : Fin 4) : Pair :=
  match line.val with
  | 0 => m.first
  | 1 => m.second
  | 2 => (m.first.1, m.second.1)
  | _ => (m.first.2, m.second.2)

abbrev Observation := Fin 4 × Pair

def squareWeights (hist : List Observation) : List Int :=
  (squareMeasure.filter fun a => hist.all fun q => readLine a.1 q.1 == q.2).map Prod.snd

theorem square_total : (squareWeights []).sum = 0 := by decide

theorem all_line_marginals : ∀ i : Fin 4, ∀ a b : Bool,
    (squareWeights [(i, (a,b))]).sum = 0 := by decide

def bitMeasure : List (Bool × Int) := [(false,1), (true,-1)]

def bitWeights (hist : List Bool) : List Int :=
  (bitMeasure.filter fun a => hist.all fun b => a.1 == b).map Prod.snd

inductive Local where
  | square (hist : List Observation)
  | bit (hist : List Bool)

def Local.cost : Local → Nat
  | .square hist => hist.length
  | .bit hist => hist.length

def Local.threshold : Local → Nat
  | .square _ => 2
  | .bit _ => 1

def Local.weights : Local → List Int
  | .square hist => squareWeights hist
  | .bit hist => bitWeights hist

theorem short_block (h : Local) (short : h.cost < h.threshold) : h.weights.sum = 0 := by
  cases h with
  | bit hist =>
    cases hist with
    | nil => decide
    | cons _ _ => simp [Local.cost, Local.threshold] at short
  | square hist =>
    cases hist with
    | nil => exact square_total
    | cons q tail =>
      cases tail with
      | nil =>
        obtain ⟨i,a,b⟩ := q
        exact all_line_marginals i a b
      | cons _ _ => simp [Local.cost, Local.threshold] at short <;> omega

/-- The complete multiset of atom weights in the Cartesian transcript cylinder. -/
def cylinderWeights : List Local → List Int
  | [] => [1]
  | h :: tail =>
    let rest := cylinderWeights tail
    h.weights.flatMap fun w => rest.map fun v => w * v

private theorem scaledSum (w : Int) (l : List Int) :
    (l.map (fun v => w * v)).sum = w * l.sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Int.mul_add]

private theorem appendSum (a b : List Int) : (a ++ b).sum = a.sum + b.sum := by
  induction a with
  | nil => simp
  | cons x a ih => simp [ih, Int.add_assoc]

private theorem productSum (a b : List Int) :
    (a.flatMap fun w => b.map fun v => w * v).sum = a.sum * b.sum := by
  induction a with
  | nil => simp
  | cons x a ih => simp [List.flatMap_cons, appendSum, scaledSum, ih, Int.add_mul]

theorem cylinder_rec (h : Local) (tail : List Local) :
    (cylinderWeights (h :: tail)).sum = h.weights.sum * (cylinderWeights tail).sum :=
  productSum _ _

/-- Histories may repeat a coordinate or prescribe contradictory answers. -/
theorem insufficient_lines : ∀ hs : List Local,
    (hs.map Local.cost).sum < (hs.map Local.threshold).sum →
    (cylinderWeights hs).sum = 0 := by
  intro hs
  induction hs with
  | nil => simp
  | cons h tail ih =>
    intro short
    simp only [List.map_cons, List.sum_cons] at short
    rw [cylinder_rec]
    by_cases localShort : h.cost < h.threshold
    · rw [short_block h localShort, Int.zero_mul]
    · have restShort : (tail.map Local.cost).sum < (tail.map Local.threshold).sum := by omega
      rw [ih restShort, Int.mul_zero]

/-- A full row read on a scalar and the two rows of a square identify the zero atom. -/
def pinZero (square : Bool) : Local :=
  if square then .square [(0,(false,false)), (1,(false,false))] else .bit [false]

theorem mass_at_zero : ∀ shape : List Bool,
    (cylinderWeights (shape.map pinZero)).sum = 1 := by
  intro shape
  induction shape with
  | nil => decide
  | cons s tail ih =>
    have localUnit : (pinZero s).weights.sum = 1 := by cases s <;> decide
    simp only [List.map_cons, cylinder_rec, localUnit, ih]
    decide

end ResidualLineWitness
