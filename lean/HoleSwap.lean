import Std

namespace HoleSwap
variable {ι α : Type}

/-- The last slot of a completed injection contains its missing value. -/
def swapAt [DecidableEq ι] (f : ι → α) (last j : ι) (k : ι) : α :=
  if k = last then f j else if k = j then f last else f k

theorem read_last [DecidableEq ι] (f : ι → α) (last j : ι) :
    swapAt f last j last = f j := by simp [swapAt]

theorem read_chosen [DecidableEq ι] (f : ι → α) (last j : ι) :
    swapAt f last j j = f last := by
  by_cases same : j = last <;> simp [swapAt, same]

theorem undo [DecidableEq ι] (f : ι → α) (last j : ι) :
    swapAt (swapAt f last j) last j = f := by
  funext k
  by_cases a : k = last
  · subst k; rw [read_last, read_chosen]
  by_cases b : k = j
  · subst k; rw [read_chosen, read_last]
  simp [swapAt, a, b]

/-- A witnessing path is represented by its finite set of reads and the
    property that matching its answers suffices to accept the candidate. -/
theorem carry_witness [DecidableEq ι] (accept : (ι → α) → α → Prop)
    (f : ι → α) (last j : ι) (probes : List ι)
    (legal : last ∉ probes) (unread : j ∉ probes)
    (replay : ∀ g, (∀ k ∈ probes, g k = f k) → accept g (f last)) :
    accept (swapAt f last j) (swapAt f last j j) := by
  rw [read_chosen]
  apply replay
  intro k hk
  have hl : k ≠ last := fun eq => legal (eq ▸ hk)
  have hj : k ≠ j := fun eq => unread (eq ▸ hk)
  simp [swapAt, hl, hj]

theorem counted_pairs_injective [DecidableEq ι] (last : ι) (a b : (ι → α) × ι)
    (eq : (swapAt a.1 last a.2, a.2) = (swapAt b.1 last b.2, b.2)) : a = b := by
  rcases a with ⟨f, j⟩
  rcases b with ⟨g, k⟩
  have eqIndex : j = k := congrArg Prod.snd eq
  subst k
  have eqFunction : swapAt f last j = swapAt g last j := congrArg Prod.fst eq
  have recovered := congrArg (fun s => swapAt s last j) eqFunction
  simp only [undo] at recovered
  exact congrArg (fun s => (s, j)) recovered

end HoleSwap
