import Std

namespace ConsecutiveNativeWinners

/-- Both programs choose from the same counterfactual search at the first
    date. The second program replays the old inputs. -/
theorem pairedFallback {A B : Type} (p : A) (q : B)
    (bad : A × B → Prop) (choice : Option (A × B))
    (searchSome : ∀ w, choice = some w → bad w)
    (searchNone : choice = none → ∀ w, ¬bad w)
    (left : A) (right : B)
    (firstReport : left = (choice.getD (p,q)).1)
    (secondReport : right = (choice.getD (p,q)).2)
    (soundOnTrueWinners : ¬bad (left,right)) :
    left = p ∧ right = q ∧ ∀ w, ¬bad w := by
  cases hc : choice with
  | none => simpa [hc] using
      And.intro firstReport (And.intro secondReport (searchNone hc))
  | some trial =>
    have eq : (left,right) = trial := by
      simp only [hc, Option.getD] at firstReport secondReport
      rw [firstReport, secondReport]
    exact False.elim (soundOnTrueWinners (eq ▸ searchSome trial hc))

private theorem countDistinct {xs pool : List Nat} (nd : xs.Nodup)
    (inside : ∀ x ∈ xs, x ∈ pool) : xs.length ≤ pool.length := by
  induction xs generalizing pool with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp nd
    have mem := inside x (by simp)
    have pos := List.length_pos_of_mem mem
    have bound := ih tail (pool := pool.erase x) (by
      intro y hy
      have diff : y ≠ x := fun he => fresh (he ▸ hy)
      exact (List.mem_erase_of_ne diff).mpr (inside y (by simp [hy])))
    rw [List.length_erase_of_mem mem] at bound
    simp
    omega

/-- Each date listed is a real first-partner award. Its successor's winner is
    either the terminal or a smaller rank. Retirement makes winners distinct
    on distinct successor dates. -/
theorem terminalAfterPartner (f : Nat) (firstDates : List Nat) (nextWinner : Nat → Nat)
    (enough : f < firstDates.length) (distinctDates : firstDates.Nodup)
    (eligible : ∀ i ∈ firstDates, nextWinner (i+1) ≤ f)
    (retire : ∀ i ∈ firstDates, ∀ j ∈ firstDates,
      nextWinner (i+1) = nextWinner (j+1) → i+1 = j+1) :
    ∃ i ∈ firstDates, nextWinner (i+1) = f := by
  apply Classical.byContradiction
  intro missing
  let blockers := firstDates.map (fun i => nextWinner (i+1))
  have unique : blockers.Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ distinctDates
    intro i j hi hj diff same
    exact diff (Nat.succ.inj (retire i hi j hj same))
  have bounded : ∀ b ∈ blockers, b ∈ List.range f := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have le := eligible i hi
    have ne : nextWinner (i+1) ≠ f := fun eq => missing ⟨i,hi,eq⟩
    exact List.mem_range.mpr (by omega)
  have size := countDistinct unique bounded
  simp [blockers] at size
  omega

end ConsecutiveNativeWinners
