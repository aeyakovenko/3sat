import Std

namespace AffineReadForestGap

/-- Graft a child root to a parent root by a new edge. The parent root remains
    the root of the result. The two input trees have disjoint vertex sets. -/
inductive Tree where
  | vertex
  | graft (parent child : Tree)

def vertices : Tree → Nat
  | .vertex => 1
  | .graft a b => vertices a + vertices b

/-- Flag = the root is in the independent set. -/
inductive Independent : Tree → Bool → Nat → Prop where
  | leave : Independent .vertex false 0
  | take : Independent .vertex true 1
  | graft {a b x y i j} (left : Independent a x i) (right : Independent b y j)
      (compatible : (x && y) = false) : Independent (.graft a b) x (i+j)

/-- Flag = the root is incident to a selected matching edge. -/
inductive Matching : Tree → Bool → Nat → Prop where
  | vertex : Matching .vertex false 0
  | skip {a b x y i j} (left : Matching a x i) (right : Matching b y j) :
      Matching (.graft a b) x (i+j)
  | bridge {a b i j} (left : Matching a false i) (right : Matching b false j) :
      Matching (.graft a b) true (i+j+1)

private def spare (selected used : Bool) : Nat :=
  if selected || used then 0 else 1

/-- Charge a matching edge to an endpoint outside the independent set.
    The root is separately available if neither witness uses it. -/
private theorem jointBound (tree : Tree) (ind : Independent tree x i) (mt : Matching tree y j) :
    i+j+spare x y ≤ vertices tree := by
  induction tree generalizing x y i j with
  | vertex =>
    cases ind <;> cases mt <;> decide
  | graft a b ihA ihB =>
    cases ind with
    | @graft _ _ sx sy ci cj ix iy good =>
      cases mt with
      | @skip _ _ mx my mi mj ma mb =>
        have l := ihA ix ma
        have r := ihB iy mb
        change ci+cj+(mi+mj)+spare x y ≤ vertices a + vertices b
        omega
      | @bridge _ _ mi mj ma mb =>
        have l := ihA ix ma
        have r := ihB iy mb
        cases x <;> cases sy <;> simp [spare, vertices] at * <;> omega

private theorem dropRoot (tree : Tree) (ind : Independent tree true i) :
    ∃ k, i = k+1 ∧ Independent tree false k := by
  induction tree generalizing i with
  | vertex =>
    cases ind
    exact ⟨0,rfl,.leave⟩
  | graft a b ih _ =>
    cases ind with
    | @graft _ _ _ sy ci cj ix iy good =>
      obtain ⟨k, sz, reduced⟩ := ih ix
      exact ⟨k+cj, by omega, .graft reduced iy rfl⟩

/-- Tight, constructed witnesses. When both roots were selected, remove the
    parent root and use the bridge between two previously unmatched roots. -/
private theorem treeWitness (tree : Tree) :
    ∃ flag i j, Independent tree flag i ∧ Matching tree (!flag) j ∧ i+j = vertices tree := by
  induction tree with
  | vertex => exact ⟨true,1,0,.take,.vertex,rfl⟩
  | graft a b ihA ihB =>
    obtain ⟨x,i,j,ix,mx,ax⟩ := ihA
    obtain ⟨y,k,l,iy,my,ay⟩ := ihB
    cases x <;> cases y
    · exact ⟨false, i+k, j+l, .graft ix iy rfl, .skip mx my, by simp [vertices]; omega⟩
    · exact ⟨false, i+k, j+l, .graft ix iy rfl, .skip mx my, by simp [vertices]; omega⟩
    · exact ⟨true, i+k, j+l, .graft ix iy rfl, .skip mx my, by simp [vertices]; omega⟩
    · obtain ⟨u, sz, reduced⟩ := dropRoot a ix
      exact ⟨false,u+k,j+l+1,.graft reduced iy rfl,.bridge mx my,by simp [vertices]; omega⟩

def forestSize (trees : List Tree) : Nat := (trees.map vertices).sum

/-- A disjoint union adds cardinalities. Flags are local to components. -/
inductive Across (family : Tree → Bool → Nat → Prop) : List Tree → Nat → Prop where
  | nil : Across family [] 0
  | cons {tree rest flag here tail} (one : family tree flag here) (others : Across family rest tail) :
      Across family (tree :: rest) (here+tail)

theorem forestBound {trees : List Tree} (ind : Across Independent trees i) (mt : Across Matching trees j) :
    i+j ≤ forestSize trees := by
  induction ind generalizing j with
  | nil => cases mt; decide
  | @cons tree rest flag here tail one others ih =>
    cases mt with
    | cons first later =>
      have localBound := jointBound tree one first
      have tailBound := ih later
      change _ ≤ vertices tree + forestSize rest
      omega

private theorem forestWitness (trees : List Tree) :
    ∃ i j, Across Independent trees i ∧ Across Matching trees j ∧ i+j = forestSize trees := by
  induction trees with
  | nil => exact ⟨0,0,.nil,.nil,rfl⟩
  | cons tree rest ih =>
    obtain ⟨flag,i,j,ii,mj,eq⟩ := treeWitness tree
    obtain ⟨k,l,ik,ml,restEq⟩ := ih
    refine ⟨i+k,j+l,.cons ii ik,.cons mj ml,?_⟩
    change _ = vertices tree + forestSize rest
    omega

/-- Construct extremizers of both optimization problems on every forest. -/
theorem forestDuality (trees : List Tree) :
    ∃ α ν, Across Independent trees α ∧ Across Matching trees ν ∧ α+ν = forestSize trees ∧
      (∀ i, Across Independent trees i → i ≤ α) ∧
      (∀ j, Across Matching trees j → j ≤ ν) := by
  obtain ⟨α,ν,ind,mt,eq⟩ := forestWitness trees
  refine ⟨α,ν,ind,mt,eq,?_,?_⟩
  · intro i witness
    have bound := forestBound witness mt
    omega
  · intro j witness
    have bound := forestBound ind witness
    omega

def treeEdges : Tree → Nat
  | .vertex => 0
  | .graft a b => treeEdges a + treeEdges b + 1

def edgeCount (trees : List Tree) : Nat := (trees.map treeEdges).sum

private theorem matchingCost {tree : Tree} (mt : Matching tree y j) : j ≤ treeEdges tree := by
  induction mt with
  | vertex => decide
  | skip _ _ ihA ihB => simp only [treeEdges]; omega
  | bridge _ _ ihA ihB => simp only [treeEdges]; omega

private theorem forestCost {trees : List Tree} (mt : Across Matching trees j) : j ≤ edgeCount trees := by
  induction mt with
  | nil => decide
  | @cons tree rest flag here tail one others ih =>
    have cost := matchingCost one
    change here+tail ≤ treeEdges tree + edgeCount rest
    omega

/-- In an acyclic subgraph, the ambient matching bound and the actual
    stored edge count both yield constructive independent-set certificates.
    Consequently a target bounding all independent sets needs ≥n−target edges. -/
theorem forestCertificateFloor (trees : List Tree) (ambientMatching : Nat)
    (embedded : ∀ j, Across Matching trees j → j ≤ ambientMatching) :
    ∃ i, Across Independent trees i ∧ forestSize trees - ambientMatching ≤ i ∧
      forestSize trees - edgeCount trees ≤ i := by
  obtain ⟨i,j,ind,mt,eq⟩ := forestWitness trees
  have cost := forestCost mt
  have limit := embedded j mt
  exact ⟨i,ind,by omega,by omega⟩

/-- This edge lower bound also applies when the target is the affine-output
    optimum, since every independent set supplies a zero coordinate subspace. -/
theorem necessaryEdges (trees : List Tree) (target : Nat)
    (upper : ∀ i, Across Independent trees i → i ≤ target) :
    forestSize trees - target ≤ edgeCount trees := by
  obtain ⟨i,j,ind,mt,eq⟩ := forestWitness trees
  have cost := forestCost mt
  have bound := upper i ind
  omega

/-- An independent mask on the endpoints of a disjoint matching. On every
    edge the allowed vertex subsets are exactly ∅, {left}, and {right}. -/
inductive PairMask where
  | neither | left | right

def occupied : PairMask → Nat
  | .neither => 0
  | _ => 1

def missed : PairMask → Bool
  | .neither => true
  | _ => false

def mass (mask : List PairMask) : Nat := (mask.map occupied).sum

def credit (b : Bool) : Nat := if b then 1 else 0

/-- A complementary edge has both endpoints unselected and costs ≥1
    relative to the one-per-edge maximum. -/
theorem pairScore (mask : List PairMask) :
    mass mask + credit (mask.any missed) ≤ mask.length := by
  induction mask with
  | nil => decide
  | cons p rest ih =>
    cases p <;> cases h : rest.any missed <;>
      simp [mass, occupied, credit, missed, h] at * <;> omega

/-- Maximizing an independent mask precludes a complementary edge.
    The argument `isolated` counts the selected isolated vertices. -/
theorem maximumMaskHasIndependentComplement (mask : List PairMask) (isolated allIsolated : Nat)
    (available : isolated ≤ allIsolated)
    (full : isolated+mass mask = allIsolated+mask.length) : mask.any missed = false := by
  have bound := pairScore mask
  cases h : mask.any missed with
  | false => rfl
  | true => rw [h] at bound; change mass mask + 1 ≤ mask.length at bound; omega

/-- The affine certificate score of an independent set is its size plus
    one exactly when the complementary vertices span an edge. -/
def score (isolated : Nat) (mask : List PairMask) : Nat :=
  isolated+mass mask+credit (mask.any missed)

theorem scoreUpper (mask : List PairMask) (isolated allIsolated : Nat)
    (available : isolated ≤ allIsolated) : score isolated mask ≤ allIsolated+mask.length := by
  have bound := pairScore mask
  unfold score
  omega

private theorem allLeft (m : Nat) :
    mass (List.replicate m PairMask.left) = m ∧ (List.replicate m PairMask.left).any missed = false := by
  induction m with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    simp [List.replicate_succ, mass, occupied, missed] at *
    omega

/-- Taking one endpoint of each edge and every isolated vertex attains the
    upper bound on the affine certificate score. -/
theorem scoreAttained (isolated m : Nat) :
    score isolated (List.replicate m PairMask.left) = isolated+m := by
  obtain ⟨hm, zero⟩ := allLeft m
  rw [score, hm, zero]
  rfl

/-- From an actual maximum matching of size ν one may take any prefix.
    These arithmetical witnesses give every target in [n−ν,n], with exactly
    n−target edges. Disjoint edges occupy two vertices per retained edge. -/
theorem matchingPrefixScore (n ν target : Nat) (fit : 2*ν ≤ n)
    (lower : n-ν ≤ target) (upper : target ≤ n) :
    ∃ m, m ≤ ν ∧ m = n-target ∧ 2*m ≤ n ∧
      score (n-2*m) (List.replicate m PairMask.left) = target ∧
      (∀ isolated mask, isolated ≤ n-2*m → mask.length = m → score isolated mask ≤ target) := by
  refine ⟨n-target, by omega, rfl, by omega, ?_, ?_⟩
  · rw [scoreAttained]; omega
  · intro isolated mask available size
    have bound := scoreUpper mask _ _ available
    omega

/-- The minimizing edge list is literally an initial segment of the given
    maximum matching. Its affine certificate attains the desired target. -/
theorem explicitPrefix {E : Type} (matching : List E) (n target : Nat)
    (fit : 2*matching.length ≤ n) (lower : n-matching.length ≤ target) (upper : target ≤ n) :
    ∃ kept, List.IsPrefix kept matching ∧ kept.length = n-target ∧
      score (n-2*kept.length) (List.replicate kept.length PairMask.left) = target ∧
      (∀ isolated mask, isolated ≤ n-2*kept.length → mask.length = kept.length →
        score isolated mask ≤ target) := by
  obtain ⟨m,limit,size,_,first,last⟩ := matchingPrefixScore n matching.length target fit lower upper
  have count : (matching.take m).length = m := by
    rw [List.length_take, Nat.min_eq_left limit]
  refine ⟨matching.take m, List.take_prefix m matching, count.trans size, ?_, ?_⟩
  · rw [count]; exact first
  · rw [count]; exact last

end AffineReadForestGap
