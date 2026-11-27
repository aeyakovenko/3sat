import Std

namespace AdaptiveWinnerMenus

/-- One name works on every challenge precisely when each full vector of
    row-specific challenges leaves a name with an accepting reply. -/
theorem adaptive_name {Name Challenge Reply : Type}
    (accept : Name → Challenge → Reply → Prop) :
    (∀ challenges : Name → Challenge, ∃ x p, accept x (challenges x) p) ↔
      ∃ x, ∀ c, ∃ p, accept x c p := by
  classical
  constructor
  · intro covers
    apply Classical.byContradiction
    intro missing
    have bad (x : Name) : ∃ c, ∀ p, ¬accept x c p := by
      apply Classical.byContradiction
      intro none
      apply missing
      refine ⟨x, fun c => ?_⟩
      apply Classical.byContradiction
      intro noReply
      exact none ⟨c, fun p hp => noReply ⟨p,hp⟩⟩
    let challenges := fun x => Classical.choose (bad x)
    obtain ⟨x,p,h⟩ := covers challenges
    exact Classical.choose_spec (bad x) p h
  · rintro ⟨x, all⟩ c
    obtain ⟨p, h⟩ := all (c x)
    exact ⟨x,p,h⟩

/-- Failing surjectivity admits rows accepting every generated vector even
    though each row rejects one challenge. -/
theorem missed_vector {Name Challenge Seed : Type}
    (generate : Seed → Name → Challenge) (target : Name → Challenge)
    (missing : ∀ s, generate s ≠ target) :
    (∀ s, ∃ x, generate s x ≠ target x) ∧ ¬(∃ x, ∀ c, c ≠ target x) := by
  classical
  refine ⟨fun s => ?_, ?_⟩
  · apply Classical.byContradiction
    intro noName
    apply missing s
    funext x
    exact Classical.byContradiction (fun ne => noName ⟨x,ne⟩)
  · rintro ⟨x, h⟩
    exact h (target x) rfl

/-- With finite tapes, exact threshold counting extracts one fixed name
    even if several names have replies on the same tape. The first premise
    is the union bound on the number of tapes with some accepting reply. -/
theorem count_names (hits : List Nat) (threshold successes : Nat)
    (cover : successes ≤ hits.sum)
    (enough : hits.length * threshold < successes) :
    ∃ h ∈ hits, threshold < h := by
  classical
  apply Classical.byContradiction
  intro noName
  have all : ∀ h ∈ hits, h ≤ threshold := by
    intro h hh
    exact Nat.le_of_not_gt (fun large => noName ⟨h, hh, large⟩)
  have bound (xs : List Nat) (ok : ∀ x ∈ xs, x ≤ threshold) :
      xs.sum ≤ xs.length * threshold := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have single := ok x (by simp)
      have rest := ih (fun y hy => ok y (by simp [hy]))
      simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add single rest
  exact (Nat.not_lt_of_ge (Nat.le_trans cover (bound hits all))) enough

section Pool
variable {Name Witness : Type} (checked : Name → Witness → Prop)
  (event : Name → Prop) (wins : Prop)

/-- A single rejected search row suffices for a sound exclusion; complete
    search at a winning tag supplies this universal check for every row. -/
theorem complementary_check
    (real : ∀ x, event x → ∃ u, checked x u)
    (clean : wins → ∀ x, ¬∃ u, checked x u) :
    (∀ x, (∀ u, ¬checked x u) → ¬event x) ∧
    (wins → ∀ x u, ¬checked x u) := by
  constructor
  · intro x empty hx
    obtain ⟨u, hu⟩ := real x hx
    exact empty u hu
  · intro hwin x u hu
    exact clean hwin x ⟨u,hu⟩

end Pool

/-- On a completed phase, each preempted response spends one pool name and
    each successful response spends two. An unqualified tag forces errors. -/
theorem qualifier_or_many_errors (e outside pool survivors single double errors threshold : Nat)
    (partition : e = outside + pool)
    (retirements : pool = survivors + single + 2 * double)
    (charges : single ≤ outside) (mistakes : double ≤ errors) :
    threshold ≤ survivors ∨ e + 1 ≤ threshold + 2 * outside + 2 * errors := by
  omega

/-- With the initial half-prefix qualification, the error count satisfies
    4*(errors+outside)>e on every unqualified tag in a matched phase. -/
theorem quarter_error_lower (e outside pool survivors single double errors : Nat)
    (partition : e = outside + pool)
    (retirements : pool = survivors + single + 2 * double)
    (charges : single ≤ outside) (mistakes : double ≤ errors)
    (unqualified : survivors < (e+1)/2) :
    e < 4 * (errors + outside) := by
  have enough := qualifier_or_many_errors e outside pool survivors single double errors
    ((e+1)/2) partition retirements charges mistakes
  omega

/-- Making today's first name differ from yesterday's proposed second
    prevents both claims from being false, even across a mode switch. -/
theorem adjacent_errors_impossible {α : Type} {previousSecond currentFirst winner : α}
    (guard : currentFirst ≠ previousSecond) (earlier : winner = previousSecond)
    (later : winner = currentFirst) : False := guard (later.symm.trans earlier)

/-- Before the last erroneous start all earlier errors retired two names;
    the current guard must still find its required live prefix. -/
theorem tolerant_rule_upper (e errors threshold : Nat)
    (guardAtLast : 0 < errors → 2 * (errors-1) + threshold ≤ e) :
    errors ≤ (e-threshold)/2 + 1 := by
  by_cases h : 0 < errors
  · have bound := guardAtLast h
    omega
  · omega

theorem retrospective_bit (first second cap : Nat) (joint : first + second ≤ cap) :
    min first second ≤ cap / 2 := by omega

theorem mistaken_bit (endpoint outside selected other : Nat)
    (forced : endpoint < 4 * (selected + outside))
    (joint : selected + other ≤ endpoint / 4 + 1)
    (large : 8 * outside + 8 ≤ endpoint) : other < selected := by omega

/-- Only the answer for the earlier name is needed to choose a safe name. -/
theorem choose_with_one_answer {Name : Type} (x y : Name) (earlierAccepted : Prop)
    [Decidable earlierAccepted] (event : Name → Prop)
    (realEarlier : event x → earlierAccepted)
    (blocksLater : earlierAccepted → ¬event y) :
    ¬event (if earlierAccepted then y else x) := by
  by_cases yes : earlierAccepted
  · simpa [yes] using blocksLater yes
  · simpa [yes] using (fun h : event x => yes (realEarlier h))

/-- The control-free normal transition either awards the tag immediately,
    or awards both selected names and resumes at the following normal date. -/
inductive CleanRun : Nat → Nat → Nat → Nat → List Nat → Prop where
  | tag (date live : Nat) : CleanRun date live date live []
  | pair {date live win survivors : Nat} {starts : List Nat} :
      CleanRun (date+2) live win survivors starts →
      CleanRun date (live+2) win survivors (date :: starts)

def blockStarts (date : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => date :: blockStarts (date+2) n

/-- The complete list of false-exclusion starts in these episodes has no
    missing block. The tag date and the remaining pool size are exact. -/
theorem clean_burst {date live win survivors : Nat} {starts : List Nat}
    (run : CleanRun date live win survivors starts) :
    starts = blockStarts date starts.length ∧
      win = date + 2 * starts.length ∧ live = survivors + 2 * starts.length := by
  induction run with
  | tag => simp [blockStarts]
  | pair previous ih =>
    obtain ⟨shape, dateEq, sizeEq⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_cons, blockStarts, List.cons.injEq, true_and]
      exact shape
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega

end AdaptiveWinnerMenus
