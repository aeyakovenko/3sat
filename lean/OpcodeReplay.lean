import Std

namespace OpcodeReplay

variable {State Query : Type}

def path (advance : Nat → State → State) (initial : State) : Nat → State
  | 0 => initial
  | t + 1 => advance t (path advance initial t)

def supply (ask : State → Option Query) (oracle : Query → Bool) (s : State) : Bool :=
  match ask s with
  | none => false
  | some q => oracle q

def proposed (ask : State → Option Query) (answers : Nat → Bool) (t : Nat)
    (s : State) : Bool :=
  match ask s with
  | none => false
  | some _ => answers t

def actual (ask : State → Option Query) (step : State → Bool → State)
    (oracle : Query → Bool) (s : State) : Nat → State :=
  path (fun _ x => step x (supply ask oracle x)) s

def replay (ask : State → Option Query) (step : State → Bool → State)
    (answers : Nat → Bool) (s : State) : Nat → State :=
  path (fun t x => step x (proposed ask answers t x)) s

def consistent (ask : State → Option Query) (step : State → Bool → State)
    (oracle : Query → Bool) (answers : Nat → Bool) (s : State) (n : Nat) : Prop :=
  ∀ t, t < n → ∀ q, ask (replay ask step answers s t) = some q → answers t = oracle q

theorem consistent_replay (ask : State → Option Query) (step : State → Bool → State)
    (oracle : Query → Bool) (answers : Nat → Bool) (s : State) (n : Nat)
    (ok : consistent ask step oracle answers s n) :
    replay ask step answers s n = actual ask step oracle s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have early : consistent ask step oracle answers s n :=
      fun t h q test => ok t (Nat.lt_trans h (Nat.lt_succ_self n)) q test
    have agreeState := ih early
    change step (replay ask step answers s n) (proposed ask answers n (replay ask step answers s n)) =
      step (actual ask step oracle s n) (supply ask oracle (actual ask step oracle s n))
    rw [← agreeState]
    unfold proposed supply
    cases h : ask (replay ask step answers s n) with
    | none => rfl
    | some q => rw [ok n (Nat.lt_succ_self n) q h]

theorem honest_chart (ask : State → Option Query) (step : State → Bool → State)
    (oracle : Query → Bool) (s : State) :
    ∃ answers, ∀ n, consistent ask step oracle answers s n := by
  let answers := fun t => supply ask oracle (actual ask step oracle s t)
  refine ⟨answers, ?_⟩
  intro n
  induction n with
  | zero => intro t ht; omega
  | succ n ih =>
    intro t ht q test
    by_cases earlier : t < n
    · exact ih t earlier q test
    · have eq : t = n := by omega
      subst t
      rw [consistent_replay ask step oracle answers s n ih] at test
      exact show supply ask oracle (actual ask step oracle s n) = oracle q by
        simp [supply, test]

theorem run_iff (ask : State → Option Query) (step : State → Bool → State)
    (oracle : Query → Bool) (s : State) (n : Nat) (accepts : State → Prop) :
    accepts (actual ask step oracle s n) ↔
      ∃ answers, consistent ask step oracle answers s n ∧ accepts (replay ask step answers s n) := by
  constructor
  · intro yes
    obtain ⟨answers, verified⟩ := honest_chart ask step oracle s
    exact ⟨answers, verified n, (consistent_replay ask step oracle answers s n (verified n)).symm ▸ yes⟩
  · rintro ⟨answers, verified, yes⟩
    simpa only [consistent_replay ask step oracle answers s n verified] using yes

theorem dictionary_test {Code : Type} (decode : Code → Query → Bool)
    (oracle : Query → Bool) (hasCode : ∃ d, ∀ q, decode d q = oracle q)
    (verdict : (Query → Bool) → Prop) :
    verdict oracle ↔ ∃ d, (∀ q, decode d q = oracle q) ∧ verdict (decode d) := by
  constructor
  · intro yes
    obtain ⟨d, exactAt⟩ := hasCode
    exact ⟨d, exactAt, (funext exactAt).symm ▸ yes⟩
  · rintro ⟨d, exactAt, yes⟩
    simpa only [funext exactAt] using yes


/-- At a fixed width, at most one visible stage can still be unpublished. -/
theorem at_most_one_unpublished (visibleFrom finishedAt : Nat → Nat)
    (spaced : ∀ i j, i < j → finishedAt i < visibleFrom j) (w i j : Nat)
    (vi : visibleFrom i ≤ w) (vj : visibleFrom j ≤ w)
    (ui : w < finishedAt i) (uj : w < finishedAt j) : i = j := by
  by_cases lt : i < j
  · have := spaced i j lt
    omega
  · by_cases gt : j < i
    · have := spaced j i gt
      omega
    · omega

/-- At least a sixth of the tapes hit the cutoff when truncation lowers
    honest acceptance from two thirds to at most one half. -/
theorem cutoff_count (tapes honest clipped hit : Nat)
    (complete : 2 * tapes ≤ 3 * honest) (below : 2 * clipped ≤ tapes)
    (coupled : honest ≤ clipped + hit) : tapes ≤ 6 * hit := by
  omega

/-- The tapes that hit a step limit each contribute its full cost. -/
theorem cutoff_work (work : List Nat) (limit : Nat) :
    limit * (work.filter (fun v => decide (limit ≤ v))).length ≤ work.sum := by
  induction work with
  | nil => simp
  | cons v tail ih =>
    by_cases h : limit ≤ v
    · simp [List.filter_cons, h, Nat.mul_add]
      omega
    · simp [List.filter_cons, h]
      omega

end OpcodeReplay
