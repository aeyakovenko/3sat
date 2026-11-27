import Std

namespace GapEditMonitors

/-- An edit overwrites one named bit. A second write to that name replaces the first. -/
structure Edit (Name : Type) where
  name : Name
  value : Bool

def update {Name Slot : Type} [DecidableEq Name] (watched : Slot → Name)
    (state : Slot → Bool) (edit : Edit Name) (slot : Slot) : Bool :=
  if watched slot = edit.name then edit.value else state slot

def replay {Name Slot : Type} [DecidableEq Name] (watched : Slot → Name)
    (initial : Slot → Bool) (edits : List (Edit Name)) : Slot → Bool :=
  edits.foldl (update watched) initial

/-- Independent copies of each watched bit remain exactly the projection of the full state,
    including repeated variables and arbitrary overwrites at watched or unwatched names. -/
theorem replay_projection {Name Slot : Type} [DecidableEq Name] (watched : Slot → Name)
    (initial : Name → Bool) (edits : List (Edit Name)) (slot : Slot) :
    replay watched (initial ∘ watched) edits slot = replay id initial edits (watched slot) := by
  induction edits generalizing initial with
  | nil => rfl
  | cons edit tail ih =>
    change replay watched (update watched (initial ∘ watched) edit) tail slot =
      replay id (update id initial edit) tail (watched slot)
    exact ih (update id initial edit)

/-- Any finite prefix yields the correct truth value for every signed 3-clause in one
    fixed directory. A literal's polarity is the bit making the literal true. -/
theorem watched_clause {Name Index : Type} [DecidableEq Name]
    (clause : Index → Fin 3 → Name × Bool) (initial : Name → Bool)
    (edits : List (Edit Name)) (i : Index) :
    let key : Index × Fin 3 → Name := fun pos => (clause pos.1 pos.2).1
    (∃ j, replay key (initial ∘ key) edits (i, j) = (clause i j).2) ↔
      ∃ j, replay id initial edits (clause i j).1 = (clause i j).2 := by
  dsimp only
  simp only [replay_projection]

/-- All ordered directories of length k, sampled with replacement from the clause list. -/
def directories {C : Type} (clauses : List C) : Nat → List (List C)
  | 0 => [[]]
  | k + 1 => clauses.flatMap (fun c => (directories clauses k).map (c :: ·))

private theorem listed {C : Type} (clauses : List C) (k : Nat) (d : List C) :
    d ∈ directories clauses k ↔ d.length = k ∧ ∀ c ∈ d, c ∈ clauses := by
  induction k generalizing d with
  | zero => cases d <;> simp [directories]
  | succ k ih => cases d <;> simp [directories, ih, and_left_comm]

/-- Exact number of directories missing a given candidate, with clause multiplicities. -/
theorem miss_count {C : Type} (clauses : List C) (passes : C → Bool) (k : Nat) :
    (directories clauses k).countP (fun d => d.all passes) = (clauses.countP passes)^k := by
  induction k with
  | zero => simp [directories]
  | succ k ih =>
    let tails := directories clauses k
    have extend (heads : List C) :
        (heads.flatMap (fun c => tails.map (c :: ·))).countP (fun d => d.all passes) =
          (tails.countP (fun d => d.all passes)) * heads.countP passes := by
      induction heads with
      | nil => simp
      | cons c cs rec =>
        cases hc : passes c <;>
          simp [List.countP_map, Function.comp_def, List.countP_cons, hc, rec, Nat.mul_succ,
            Nat.add_comm]
    simpa only [directories, tails, ih, Nat.pow_succ] using extend clauses

private theorem directory_count {C : Type} (clauses : List C) (k : Nat) :
    (directories clauses k).length = clauses.length^k := by
  have every (d : List C) : (d.all fun _ => true) = true := List.all_eq_true.2 (by simp)
  simpa [every] using miss_count clauses (fun _ => true) k

private theorem count_union {T A : Type} (trials : List T) (candidates : List A)
    (miss : A → T → Bool) (bound : Nat)
    (each : ∀ a ∈ candidates, trials.countP (miss a) ≤ bound) :
    trials.countP (fun t => candidates.any (fun a => miss a t)) ≤ candidates.length * bound := by
  induction candidates with
  | nil => simp
  | cons a rest ih =>
    let bad := fun t => rest.any (fun x => miss x t)
    have join : trials.countP (fun t => miss a t || bad t) ≤
          trials.countP (miss a) + trials.countP bad := by
      clear ih each
      induction trials with
      | nil => simp
      | cons t ts rec =>
        cases p : miss a t <;> cases q : bad t <;> simp [List.countP_cons, p, q] <;> omega
    have tail := ih (fun x hx => each x (by simp [hx]))
    have head := each a (by simp)
    simpa [bad, Nat.succ_mul, Nat.add_comm] using Nat.le_trans join (Nat.add_le_add head tail)

/-- Simultaneously catch every entry in a fixed finite stream. The exact integral
    condition is the union bound `number of candidates * passCap^k < clauses^k`. -/
theorem fixed_directory {C A : Type} (clauses : List C) (candidates : List A)
    (passes : A → C → Bool) (k passCap : Nat)
    (gap : ∀ a ∈ candidates, clauses.countP (passes a) ≤ passCap)
    (room : candidates.length * passCap^k < clauses.length^k) :
    ∃ dir : List C, dir.length = k ∧ (∀ c ∈ dir, c ∈ clauses) ∧
      ∀ a ∈ candidates, ∃ c ∈ dir, passes a c = false := by
  let trials := directories clauses k
  let miss := fun (a : A) (d : List C) => d.all (passes a)
  have each : ∀ a ∈ candidates, trials.countP (miss a) ≤ passCap^k := by
    intro a ha
    change (directories clauses k).countP (fun d => d.all (passes a)) ≤ passCap^k
    rw [miss_count]
    exact Nat.pow_le_pow_left (gap a ha) k
  have bound := count_union trials candidates miss (passCap^k) each
  have len : trials.length = clauses.length^k := directory_count clauses k
  have existsGood : ∃ d ∈ trials, candidates.any (fun a => miss a d) = false := by
    apply Classical.byContradiction
    intro absent
    have allMiss : trials.countP (fun d => candidates.any (fun a => miss a d)) = trials.length := by
      apply List.countP_eq_length.mpr
      intro d hd
      cases h : candidates.any (fun a => miss a d) with
      | false => exact (absent ⟨d, hd, h⟩).elim
      | true => rfl
    omega
  obtain ⟨d, hd, good⟩ := existsGood
  obtain ⟨size, contained⟩ := (listed clauses k d).1 hd
  refine ⟨d, size, contained, ?_⟩
  intro a ha
  have h : miss a d = false := by
    cases hm : miss a d with
    | false => rfl
    | true =>
      have conflict := List.any_eq_true.mpr
        (show ∃ x ∈ candidates, miss x d = true from ⟨a, ha, hm⟩)
      simp [good] at conflict
  simpa [miss] using h

end GapEditMonitors
