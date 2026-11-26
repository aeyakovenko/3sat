import Std

/-! A finite prefix trial for a proof. Internal nodes ask whether the right
subtree has an accepted proof. The verdict at any node may be arbitrary.
The file proves trace membership of a wrong query, including the signed
common-timeout consequences for finite portfolios of correct deciders.
Timing, program implementation and proof length are outside this kernel. -/

namespace FinitePortfolioProofReceipts

inductive Trial (File Proof : Type) where
  | leaf (certificate : Proof)
  | query (file : File) (no yes : Trial File Proof)

variable {File Proof : Type}

def HasProof (valid : Proof → Prop) : Trial File Proof → Prop
  | .leaf p => valid p
  | .query _ no yes => HasProof valid no ∨ HasProof valid yes

def FaithfulFiles (truth : File → Bool) (valid : Proof → Prop) :
    Trial File Proof → Prop
  | .leaf _ => True
  | .query f no yes =>
      (truth f = true ↔ HasProof valid yes) ∧
      FaithfulFiles truth valid no ∧ FaithfulFiles truth valid yes

def candidate (vote : File → Bool) : Trial File Proof → Proof
  | .leaf p => p
  | .query f no yes =>
      if vote f then candidate vote yes else candidate vote no

def queries (vote : File → Bool) : Trial File Proof → List File
  | .leaf _ => []
  | .query f no yes =>
      f :: (if vote f then queries vote yes else queries vote no)

/-- Only file answers along the actual trajectory must be correct. -/
theorem correct_trace_recovers (truth vote : File → Bool) (valid : Proof → Prop)
    (tree : Trial File Proof) (faithful : FaithfulFiles truth valid tree)
    (live : HasProof valid tree)
    (correct : ∀ f ∈ queries vote tree, vote f = truth f) :
    valid (candidate vote tree) := by
  induction tree with
  | leaf p => exact live
  | query f no yes left right =>
    obtain ⟨file, filesNo, filesYes⟩ := faithful
    have atRoot := correct f (by simp [queries])
    cases answer : vote f with
    | false =>
      have dead : ¬HasProof valid yes := by
        intro proof
        have bit := file.mpr proof
        simp_all
      have onNo : ∀ g ∈ queries vote no, vote g = truth g := by
        intro g hg
        exact correct g (by simp [queries, answer, hg])
      have recovers := left filesNo (live.elim id (fun hy => (dead hy).elim)) onNo
      simpa [candidate, answer] using recovers
    | true =>
      have onYes : ∀ g ∈ queries vote yes, vote g = truth g := by
        intro g hg
        exact correct g (by simp [queries, answer, hg])
      have recovers := right filesYes (file.mp (atRoot.symm.trans answer)) onYes
      simpa [candidate, answer] using recovers

theorem receipt_from_active_trial (truth vote : File → Bool) (valid : Proof → Prop)
    (tree : Trial File Proof) (faithful : FaithfulFiles truth valid tree)
    (live : HasProof valid tree) (rejected : ¬valid (candidate vote tree)) :
    ∃ f ∈ queries vote tree, vote f ≠ truth f := by
  classical
  apply Classical.byContradiction
  intro none
  apply rejected
  apply correct_trace_recovers truth vote valid tree faithful live
  intro f hf
  apply Classical.byContradiction
  intro wrong
  exact none ⟨f, hf, wrong⟩

/-- Either a recorded earlier failure or a wrong current prefix occurs.
The proof never assumes the trial was chosen from just one solver. -/
theorem receipt_for_every_portfolio {Portfolio : Type}
    (truth : File → Bool) (votes : Portfolio → File → Bool) (valid : Proof → Prop)
    (tree : Trial File Proof) (faithful : FaithfulFiles truth valid tree)
    (live : HasProof valid tree) (old : Portfolio → List File)
    (finished : ∀ s, (∃ f ∈ old s, votes s f ≠ truth f) ∨
      ¬valid (candidate (votes s) tree)) :
    ∀ s, ∃ f ∈ old s ++ queries (votes s) tree, votes s f ≠ truth f := by
  intro s
  rcases finished s with prev | failed
  · obtain ⟨f, h, wrong⟩ := prev
    exact ⟨f, List.mem_append_left _ h, wrong⟩
  · obtain ⟨f, h, wrong⟩ :=
      receipt_from_active_trial truth (votes s) valid tree faithful live failed
    exact ⟨f, List.mem_append_right _ h, wrong⟩

/-- The program can be one common trial at every site. A genuinely accepted
proof implies some site is quiet, while completing its acceptance latches
every site. Consequently none of the candidates whose checks finish passes. -/
theorem no_checked_candidate {Site : Type} (latched : Site → Prop)
    (valid : Proof → Prop) (p : Proof)
    (sound : valid p → ∃ z, ¬ latched z)
    (act : valid p → ∀ z, latched z) : ¬valid p := by
  intro proof
  obtain ⟨z, quiet⟩ := sound proof
  exact quiet (act proof z)

variable {Program : Type}

/-- A component returns none on timeout, and otherwise its own verdict. -/
def orVote (run : Program → Option Bool) (pool : List Program) : Bool :=
  pool.any fun i => run i == some true

def andVote (run : Program → Option Bool) (pool : List Program) : Bool :=
  !(pool.any fun i => run i == some false)

/-- A wrong OR from honest components means that every member timed out on
this very positive input. This includes the empty portfolio. -/
theorem wrong_or (truth : Bool) (run : Program → Option Bool) (pool : List Program)
    (honest : ∀ i ∈ pool, ∀ b, run i = some b → b = truth)
    (wrong : orVote run pool ≠ truth) :
    truth = true ∧ ∀ i ∈ pool, run i = none := by
  cases truth with
  | false =>
    have hit : ∃ i ∈ pool, run i = some true := by
      simpa [orVote] using wrong
    obtain ⟨i, hi, got⟩ := hit
    cases honest i hi true got
  | true =>
    refine ⟨rfl, ?_⟩
    have miss : ∀ i ∈ pool, run i ≠ some true := by
      simpa [orVote] using wrong
    intro i hi
    cases hr : run i with
    | none => rfl
    | some b =>
      have hb := honest i hi b hr
      exact False.elim (miss i hi (hb ▸ hr))

/-- A wrong AND from honest components means that every member timed out
on the same negative input. -/
theorem wrong_and (truth : Bool) (run : Program → Option Bool) (pool : List Program)
    (honest : ∀ i ∈ pool, ∀ b, run i = some b → b = truth)
    (wrong : andVote run pool ≠ truth) :
    truth = false ∧ ∀ i ∈ pool, run i = none := by
  cases truth with
  | false =>
    refine ⟨rfl, ?_⟩
    have miss : ∀ i ∈ pool, run i ≠ some false := by
      simpa [andVote] using wrong
    intro i hi
    cases hr : run i with
    | none => rfl
    | some b =>
      have hb := honest i hi b hr
      exact False.elim (miss i hi (hb ▸ hr))
  | true =>
    have hit : ∃ i ∈ pool, run i = some false := by
      simpa [andVote] using wrong
    obtain ⟨i, hi, got⟩ := hit
    cases honest i hi false got

end FinitePortfolioProofReceipts
