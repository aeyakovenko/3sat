import Std

namespace GuardedIndexedSnapshots

/-- An honest certificate about any equivalent reordering makes the auxiliary
    branch true. Every successful auxiliary verification certifies a rejection
    on some equivalent reordering, and the monitored solver is correct. -/
theorem guard_and_exclusion {X R : Type} (sat base signal : X → Prop)
    (reordered cheap : X → R → Prop)
    (layout : ∀ x, sat x ↔ base x ∨ signal x)
    (invariant : ∀ x r, reordered x r ↔ sat x)
    (certSound : ∀ x, signal x → ∃ r, ¬ reordered x r)
    (onBudget : ∀ x r, cheap x r → signal x) :
    ∀ x, (sat x ↔ base x) ∧ ¬ signal x ∧ ∀ r, ¬ cheap x r := by
  intro x
  have noSignal : ¬ signal x := by
    intro seen
    have yes := (layout x).mpr (Or.inr seen)
    obtain ⟨r, no⟩ := certSound x seen
    exact no ((invariant x r).mpr yes)
  refine ⟨⟨?_, fun h => (layout x).mpr (Or.inl h)⟩, noSignal, ?_⟩
  · intro yes
    exact ((layout x).mp yes).resolve_right noSignal
  · intro r certificate
    exact noSignal (onBudget x r certificate)

/-- If all the independent payloads were small, their directory plus their
    contents would satisfy the corresponding combined threshold. -/
theorem one_large_payload (rows : List Nat) (directory limit perCut : Nat)
    (aggregate : limit < directory + rows.sum)
    (fits : directory + rows.length * perCut ≤ limit) :
    ∃ n ∈ rows, perCut < n := by
  have smallSum (ls : List Nat) (h : ∀ n ∈ ls, n ≤ perCut) :
      ls.sum ≤ ls.length * perCut := by
    induction ls with
    | nil => simp
    | cons v vs ih =>
      have hv := h v (by simp)
      have hs := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
      simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  apply Classical.byContradiction
  intro allSmall
  have bound := smallSum rows (fun n hn => by
    apply Classical.byContradiction
    intro exceeds
    exact allSmall ⟨n, hn, by omega⟩)
  omega

end GuardedIndexedSnapshots
