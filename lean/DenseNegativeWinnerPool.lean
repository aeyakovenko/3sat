import Std

namespace DenseNegativeWinnerPool

private theorem countInside {α : Type} [DecidableEq α] {xs pool : List α}
    (unique : xs.Nodup) (inside : ∀ x ∈ xs, x ∈ pool) : xs.length ≤ pool.length := by
  induction xs generalizing pool with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp unique
    have found := inside x (by simp)
    have pos := List.length_pos_of_mem found
    have smaller := ih tail (pool := pool.erase x) (by
      intro y hy
      have ne : y ≠ x := fun eq => fresh (eq ▸ hy)
      exact (List.mem_erase_of_ne ne).mpr (inside y (by simp [hy])))
    rw [List.length_erase_of_mem found] at smaller
    simp
    omega

/-- Each spent member has its own preempting rank outside the pool. Counting
all outsiders and all spent members gives the stated exceptional-set budget. -/
theorem exceptionalCount (outside spent : List Nat) (preemptor : Nat → Nat)
    (unique : spent.Nodup) (charge : ∀ r ∈ spent, preemptor r ∈ outside)
    (distinct : ∀ r ∈ spent, ∀ s ∈ spent, preemptor r = preemptor s → r = s) :
    (outside ++ spent).length ≤ 2 * outside.length := by
  have nd : (spent.map preemptor).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ unique
    intro r s hr hs ne eq
    exact ne (distinct r hr s hs eq)
  have size := countInside (pool := outside) nd (by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
    exact charge r hr)
  simp only [List.length_map] at size
  simp only [List.length_append]
  omega

def endpoint (x : Nat) (p : Nat × Nat) : Prop := x = p.1 ∨ x = p.2

/-- A vertex cover of a matching must be at least as large as the matching.
No order on the two endpoints is required. -/
theorem matchingCount (pairs : List (Nat × Nat)) (exceptions : List Nat)
    (disjoint : pairs.Pairwise (fun p q => ∀ x, endpoint x p → ¬endpoint x q))
    (covered : ∀ p ∈ pairs, p.1 ∈ exceptions ∨ p.2 ∈ exceptions) :
    pairs.length ≤ exceptions.length := by
  let pick := fun p : Nat × Nat => if p.1 ∈ exceptions then p.1 else p.2
  have atEnd (p : Nat × Nat) : endpoint (pick p) p := by
    by_cases h : p.1 ∈ exceptions <;> simp [pick, endpoint, h]
  have inCover (p : Nat × Nat) (hp : p ∈ pairs) : pick p ∈ exceptions := by
    by_cases h : p.1 ∈ exceptions
    · simp [pick, h]
    · simpa [pick, h] using (covered p hp).resolve_left h
  have nd : (pairs.map pick).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp _ disjoint
    intro p q apart eq
    exact apart (pick p) (atEnd p) (eq ▸ atEnd q)
  have size := countInside (pool := exceptions) nd (by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact inCover p hp)
  simpa using size

private def rectangle (left right : List Nat) : List (Nat × Nat) :=
  left.flatMap fun x => right.map (fun y => (x, y))

private theorem rectangleSize (left right : List Nat) :
    (rectangle left right).length = left.length * right.length := by
  induction left with
  | nil => simp [rectangle]
  | cons x xs ih => simpa [rectangle, Nat.succ_mul, Nat.add_comm] using ih

private theorem inRectangle {x y : Nat} {left right : List Nat}
    (hx : x ∈ left) (hy : y ∈ right) : (x,y) ∈ rectangle left right :=
  List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩

/-- Ordered certified pairs in a prefix of size e lie in the two rectangles
formed by that prefix and the exception list. This includes self-pairs. -/
theorem orderedPairCount (pairs : List (Nat × Nat)) (pref exceptions : List Nat)
    (unique : pairs.Nodup) (inPref : ∀ p ∈ pairs, p.1 ∈ pref ∧ p.2 ∈ pref)
    (covered : ∀ p ∈ pairs, p.1 ∈ exceptions ∨ p.2 ∈ exceptions) :
    pairs.length ≤ 2 * exceptions.length * pref.length := by
  have size := countInside (pool := rectangle exceptions pref ++ rectangle pref exceptions)
    unique (by
      intro p hp
      obtain ⟨left, right⟩ := inPref p hp
      rcases covered p hp with exc | exc
      · exact List.mem_append_left _ (inRectangle exc right)
      · exact List.mem_append_right _ (inRectangle left exc))
  simp only [List.length_append, rectangleSize] at size
  simpa [Nat.mul_comm pref.length exceptions.length, Nat.two_mul, Nat.add_mul] using size

/-- Combine retirement accounting with the matching and ordered-pair bounds. -/
theorem poolBounds (pairs : List (Nat × Nat)) (pref outside spent : List Nat)
    (preemptor : Nat → Nat) (spentOnce : spent.Nodup)
    (charge : ∀ r ∈ spent, preemptor r ∈ outside)
    (injective : ∀ r ∈ spent, ∀ s ∈ spent, preemptor r = preemptor s → r = s)
    (inPref : ∀ p ∈ pairs, p.1 ∈ pref ∧ p.2 ∈ pref)
    (covered : ∀ p ∈ pairs, p.1 ∈ outside ++ spent ∨ p.2 ∈ outside ++ spent) :
    (pairs.Pairwise (fun p q => ∀ x, endpoint x p → ¬endpoint x q) →
      pairs.length ≤ 2 * outside.length) ∧
    (pairs.Nodup → pairs.length ≤ 4 * outside.length * pref.length) := by
  have bound := exceptionalCount outside spent preemptor spentOnce charge injective
  constructor
  · intro disjoint
    exact Nat.le_trans (matchingCount pairs _ disjoint covered) bound
  · intro unique
    have twice : 2 * (outside ++ spent).length ≤ 4 * outside.length := by omega
    exact Nat.le_trans (orderedPairCount pairs pref _ unique inPref covered)
      (Nat.mul_le_mul_right pref.length twice)

/-- Search rules normally exclude only *distinct* pairs with both ranks live.
A winner can never be its own successor, so all diagonal pairs may be certified. -/
theorem coverageOrDiagonal (p : Nat × Nat) (exceptions : List Nat)
    (live accepted : Nat → Nat → Prop)
    (unexceptional : p.1 ∉ exceptions → p.2 ∉ exceptions → live p.1 p.2)
    (miss : p.1 ≠ p.2 → live p.1 p.2 → ¬accepted p.1 p.2)
    (accept : accepted p.1 p.2) : p.1 = p.2 ∨ p.1 ∈ exceptions ∨ p.2 ∈ exceptions := by
  by_cases diagonal : p.1 = p.2
  · exact Or.inl diagonal
  by_cases left : p.1 ∈ exceptions
  · exact Or.inr (Or.inl left)
  by_cases right : p.2 ∈ exceptions
  · exact Or.inr (Or.inr right)
  exact False.elim (miss diagonal (unexceptional left right) accept)

/-- For the full list of distinct ordered pairs add e possible diagonal
pairs to the 4he off-diagonal budget. -/
theorem includingDiagonal (pairs : List (Nat × Nat)) (pref exceptions : List Nat) (h : Nat)
    (small : exceptions.length ≤ 2*h) (unique : pairs.Nodup)
    (inPref : ∀ p ∈ pairs, p.1 ∈ pref ∧ p.2 ∈ pref)
    (covered : ∀ p ∈ pairs, p.1 = p.2 ∨ p.1 ∈ exceptions ∨ p.2 ∈ exceptions) :
    pairs.length ≤ 4*h*pref.length + pref.length := by
  let diag := pref.map (fun x => (x,x))
  have size := countInside (pool := (rectangle exceptions pref ++ rectangle pref exceptions) ++ diag)
    unique (by
      intro p hp
      obtain ⟨left, right⟩ := inPref p hp
      rcases covered p hp with same | exc | exc
      · apply List.mem_append_right
        exact List.mem_map.mpr ⟨p.1, left, Prod.ext rfl same⟩
      · exact List.mem_append_left _ (List.mem_append_left _ (inRectangle exc right))
      · exact List.mem_append_left _ (List.mem_append_right _ (inRectangle left exc)))
  simp only [List.length_append, rectangleSize, diag, List.length_map] at size
  have twice : 2 * exceptions.length ≤ 4*h := by omega
  have mul := Nat.mul_le_mul_right pref.length twice
  rw [Nat.mul_comm pref.length exceptions.length] at size
  simp only [Nat.two_mul, Nat.add_mul] at mul
  omega

/-- Directed certified edges, each with two different ranks, share no vertex. -/
def certifiedMatching (certified : Nat → Nat → Prop) (edges : List (Nat × Nat)) : Prop :=
  (∀ p ∈ edges, certified p.1 p.2 ∧ p.1 ≠ p.2) ∧
    edges.Pairwise (fun p q => ∀ x, endpoint x p → ¬endpoint x q)

private theorem zipDisjoint (xs ys : List Nat) (left : xs.Nodup) (right : ys.Nodup)
    (apart : ∀ x ∈ xs, x ∉ ys) :
    (xs.zip ys).Pairwise (fun p q => ∀ x, endpoint x p → ¬endpoint x q) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      obtain ⟨freshX, ndX⟩ := List.nodup_cons.mp left
      obtain ⟨freshY, ndY⟩ := List.nodup_cons.mp right
      rw [List.zip_cons_cons, List.pairwise_cons]
      constructor
      · intro p hp z hz hz'
        obtain ⟨px, py⟩ := List.of_mem_zip hp
        rcases hz with rfl | rfl <;> rcases hz' with heq | heq
        · exact freshX (heq.symm ▸ px)
        · exact apart z (by simp) (List.mem_cons_of_mem _ (heq.symm ▸ py))
        · exact apart z (List.mem_cons_of_mem _ (heq.symm ▸ px)) (by simp)
        · exact freshY (heq.symm ▸ py)
      · exact ih ys ndX ndY (fun z hz h => apart z (List.mem_cons_of_mem _ hz)
          (List.mem_cons_of_mem _ h))

/-- Complete certification from all outsiders to at least as many disjoint
pool ranks makes zip a matching saturating every outsider. -/
theorem completeBipartiteMatching (xs ys : List Nat) (certified : Nat → Nat → Prop)
    (left : xs.Nodup) (right : ys.Nodup) (apart : ∀ x ∈ xs, x ∉ ys)
    (enough : xs.length ≤ ys.length) (complete : ∀ x ∈ xs, ∀ y ∈ ys, certified x y) :
    certifiedMatching certified (xs.zip ys) ∧ (xs.zip ys).length = xs.length := by
  refine ⟨⟨?_, zipDisjoint xs ys left right apart⟩, ?_⟩
  · intro p hp
    obtain ⟨hx, hy⟩ := List.of_mem_zip hp
    exact ⟨complete _ hx _ hy, fun eq => apart _ hx (eq.symm ▸ hy)⟩
  · simp [List.length_zip, Nat.min_eq_left enough]

/-- If outsiders cover every certified off-diagonal edge, the complete
bipartite matching reaches the exact maximum. -/
theorem exactOutsideMatching (xs ys : List Nat) (certified : Nat → Nat → Prop)
    (left : xs.Nodup) (right : ys.Nodup) (apart : ∀ x ∈ xs, x ∉ ys)
    (enough : xs.length ≤ ys.length)
    (complete : ∀ x ∈ xs, ∀ y ∈ ys, certified x y)
    (cover : ∀ x y, certified x y → x ≠ y → x ∈ xs ∨ y ∈ xs) :
    certifiedMatching certified (xs.zip ys) ∧ (xs.zip ys).length = xs.length ∧
    ∀ edges, certifiedMatching certified edges → edges.length ≤ xs.length := by
  obtain ⟨witness, size⟩ := completeBipartiteMatching xs ys certified left right apart enough complete
  refine ⟨witness, size, ?_⟩
  intro edges hm
  obtain ⟨allCertified, disjoint⟩ := hm
  exact matchingCount edges xs disjoint (by
    intro p hp
    obtain ⟨accepted, diff⟩ := allCertified p hp
    exact cover _ _ accepted diff)

end DenseNegativeWinnerPool
