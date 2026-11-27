import Std

namespace RankAllocation

def Eligible (free : Nat → Prop) (lo hi i : Nat) : Prop :=
  free i ∧ lo ≤ i ∧ i ≤ hi

def First (free : Nat → Prop) (lo hi i : Nat) : Prop :=
  Eligible free lo hi i ∧ ∀ j, Eligible free lo hi j → i ≤ j

def remove (free : Nat → Prop) (taken : Nat) : Nat → Prop :=
  fun j => free j ∧ j ≠ taken

/-- Filling one slot leaves a distinct first choice unchanged. -/
theorem distinct_first {free : Nat → Prop} {lo hi x y : Nat}
    (first : First free lo hi y) (different : y ≠ x) :
    First (remove free x) lo hi y := by
  obtain ⟨⟨hy, loY, yHi⟩, least⟩ := first
  refine ⟨⟨⟨hy,different⟩,loY,yHi⟩,?_⟩
  exact fun j hj => least j ⟨hj.1.1,hj.2⟩

/-- When two intervals first choose x, every possible next choice of the
    earlier-deadline interval is also the next choice of the later one. -/
theorem collision_exchange {free : Nat → Prop} {la ra lb rb x y : Nat}
    (deadlines : ra ≤ rb) (a : First free la ra x) (b : First free lb rb x)
    (nextA : First (remove free x) la ra y) :
    First (remove free x) lb rb y := by
  obtain ⟨⟨_, lax, _⟩, leastA⟩ := a
  obtain ⟨⟨_, lbx, _⟩, leastB⟩ := b
  obtain ⟨⟨⟨freeY, diffY⟩, lay, yra⟩, leastNext⟩ := nextA
  have xy := leastA y ⟨freeY,lay,yra⟩
  refine ⟨⟨⟨freeY,diffY⟩,by omega,by omega⟩,?_⟩
  rintro j ⟨⟨freeJ,diffJ⟩,lbj,jrb⟩
  have xj := leastB j ⟨freeJ,lbj,jrb⟩
  by_cases jy : j < y
  · exact leastNext j ⟨⟨freeJ,diffJ⟩,by omega,by omega⟩
  · omega

def step (occupied : Nat → Prop) (lo hi i : Nat) : Prop :=
  occupied i ∨ First (fun j => ¬ occupied j) lo hi i

/-- Enlarging the initially occupied set can only enlarge the result
    of a first-available update. -/
theorem update_mono {s t : Nat → Prop} (sub : ∀ j, s j → t j)
    {lo hi i : Nat} (done_ : step s lo hi i) : step t lo hi i := by
  rcases done_ with haveIt | ⟨⟨_,loI,iHi⟩,least⟩
  · exact Or.inl (sub i haveIt)
  by_cases present : t i
  · exact Or.inl present
  right
  refine ⟨⟨present,loI,iHi⟩,?_⟩
  rintro j ⟨freeJ,loJ,jHi⟩
  exact least j ⟨fun sj => freeJ (sub j sj),loJ,jHi⟩

/-- On one full sweep each target still unresolved at the end is
    charged to a distinct newly filled target. -/
theorem rounds_halve {before leftover filled : Nat}
    (partition : before = leftover + filled) (charging : leftover ≤ filled) :
    2 * leftover ≤ before := by omega

theorem iterated_halving {remaining : Nat → Nat} (rounds : Nat)
    (halves : ∀ i, 2 * remaining (i+1) ≤ remaining i) :
    2^rounds * remaining rounds ≤ remaining 0 := by
  induction rounds with
  | zero => simp
  | succ r ih =>
    rw [Nat.pow_succ, Nat.mul_assoc]
    exact Nat.le_trans (Nat.mul_le_mul_left (2^r) (halves r)) ih

end RankAllocation
