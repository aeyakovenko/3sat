import Std

namespace FirstMissingCertificateLevel

variable {Code Seed : Type} [DecidableEq Code]

/-- A link at position `h` chooses a remaining code and some seed on which
    that code offers a rejection of level `h`. Removing every copy of the
    code ensures distinctness even if the supplied pool contains duplicates. -/
inductive Chain (pool : List Code) (offers : Code → Nat → Seed → Prop) :
    Nat → List Code → Prop where
  | start : Chain pool offers 0 pool
  | next {h remaining code seed} : Chain pool offers h remaining →
      code ∈ remaining → offers code h seed →
      Chain pool offers (h + 1) (remaining.filter (· != code))

/-- Truth at level `h` is witnessed by `h+1` consecutive links. -/
def Level (pool : List Code) (offers : Code → Nat → Seed → Prop) (h : Nat) : Prop :=
  ∃ remaining, Chain pool offers (h + 1) remaining

/-- A formula indexed by `z` requires that seed only at its terminal link. -/
def AtSeed (pool : List Code) (offers : Code → Nat → Seed → Prop) (h : Nat) (z : Seed) : Prop :=
  ∃ remaining c, Chain pool offers h remaining ∧ c ∈ remaining ∧ offers c h z

theorem level_iff_some_seed (pool : List Code) (offers : Code → Nat → Seed → Prop) (h : Nat) :
    Level pool offers h ↔ ∃ z, AtSeed pool offers h z := by
  constructor
  · rintro ⟨_, chain⟩
    cases chain with
    | next previous member offer => exact ⟨_, _, _, previous, member, offer⟩
  · rintro ⟨_, _, _, previous, member, offer⟩
    exact ⟨_, .next previous member offer⟩

private theorem prefix_chain {pool : List Code} {offers : Code → Nat → Seed → Prop}
    {h remaining} (chain : Chain pool offers h remaining) (i : Nat) (le : i ≤ h) :
    ∃ rest, Chain pool offers i rest := by
  induction chain with
  | start =>
    have zero : i = 0 := by omega
    exact zero ▸ ⟨_, .start⟩
  | @next h remaining code seed previous member offer ih =>
    by_cases last : i = h + 1
    · exact last ▸ ⟨_, .next previous member offer⟩
    · exact ih (by omega)

/-- A failed level leaves every later level false. -/
theorem later_absent {pool : List Code} {offers : Code → Nat → Seed → Prop}
    {i h : Nat} (le : i ≤ h) (absent : ¬ Level pool offers i) : ¬ Level pool offers h := by
  rintro ⟨remaining, chain⟩
  exact absent (prefix_chain chain (i + 1) (by omega))

private theorem chain_capacity {pool : List Code} {offers : Code → Nat → Seed → Prop}
    {h remaining} (chain : Chain pool offers h remaining) :
    h + remaining.length ≤ pool.length := by
  induction chain with
  | start => simp
  | @next h remaining code seed previous member offer ih =>
    have shrinks : (remaining.filter (· != code)).length < remaining.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨code, member, by simp⟩
    omega

/-- A code consumed by a prefix offered on an earlier level. That very prefix
    up to and including its link is a witness for the earlier level's truth. -/
private theorem consumed {pool : List Code} {offers : Code → Nat → Seed → Prop}
    {h remaining} (chain : Chain pool offers h remaining) {c : Code} (inPool : c ∈ pool)
    (gone : c ∉ remaining) : ∃ i < h, ∃ z, offers c i z ∧ AtSeed pool offers i z := by
  induction chain with
  | start => exact False.elim (gone inPool)
  | @next h remaining code seed previous member offer ih =>
    by_cases same : c = code
    · subst c
      exact ⟨h, Nat.lt_succ_self h, seed, offer, _, _, previous, member, offer⟩
    · have absent : c ∉ remaining := fun hc =>
        gone (List.mem_filter.mpr ⟨hc, by simpa using same⟩)
      obtain ⟨i, hi, z, proof⟩ := ih absent
      exact ⟨i, by omega, z, proof⟩

private theorem earliest_missing (P : Nat → Prop) (u : Nat) (missing : ¬ P u) :
    ∃ j ≤ u, ¬ P j ∧ ∀ i < j, P i := by
  induction u using Nat.strongRecOn with
  | ind u ih =>
    classical
    by_cases earlier : ∃ i < u, ¬ P i
    · obtain ⟨i, hi, no⟩ := earlier
      obtain ⟨j, hj, absent, before⟩ := ih i hi no
      exact ⟨j, by omega, absent, before⟩
    · exact ⟨u, Nat.le_refl _, missing, fun i hi =>
        Classical.byContradiction (fun no => earlier ⟨i, hi, no⟩)⟩

theorem first_missing (pool : List Code) (offers : Code → Nat → Seed → Prop) :
    ∃ j ≤ pool.length, (¬ Level pool offers j) ∧ (∀ i < j, Level pool offers i) ∧
      ∀ c ∈ pool, (∀ i < j, ∀ z, offers c i z → ¬ AtSeed pool offers i z) →
        ∀ z, ¬ offers c j z := by
  have past : ¬ Level pool offers pool.length := by
    rintro ⟨remaining, chain⟩
    have := chain_capacity chain
    omega
  obtain ⟨j, bound, missing, before⟩ := earliest_missing _ _ past
  refine ⟨j, bound, missing, before, ?_⟩
  intro c member sound z offer
  have previousLevel : ∃ remaining, Chain pool offers j remaining := by
    cases j with
    | zero => exact ⟨_, .start⟩
    | succ i => exact before i (Nat.lt_succ_self i)
  obtain ⟨remaining, chain⟩ := previousLevel
  by_cases available : c ∈ remaining
  · exact missing ⟨_, .next chain available offer⟩
  · obtain ⟨i, hi, priorSeed, priorOffer, trueLevel⟩ := consumed chain member available
    exact sound i hi priorSeed priorOffer trueLevel

/-- If a formula realizes its own terminal-seed predicate, the first level
    missing at every seed defeats every earlier-sound code on every seed. -/
theorem realized_formulas (pool : List Code) (offers : Code → Nat → Seed → Prop)
    (sat : Nat → Seed → Prop)
    (realizes : ∀ h ≤ pool.length, ∀ z, sat h z ↔ AtSeed pool offers h z) :
    ∃ j ≤ pool.length, (∀ z, ¬ sat j z) ∧ (∀ i < j, ∃ z, sat i z) ∧
      ∀ c ∈ pool, (∀ i < j, ∀ z, offers c i z → ¬ sat i z) → ∀ z, ¬ offers c j z := by
  obtain ⟨j, bound, absent, before, defeats⟩ := first_missing pool offers
  refine ⟨j, bound, ?_, ?_, ?_⟩
  · intro z yes
    exact absent ((level_iff_some_seed pool offers j).mpr ⟨z, (realizes j bound z).mp yes⟩)
  · intro i hi
    obtain ⟨z, yes⟩ := (level_iff_some_seed pool offers i).mp (before i hi)
    exact ⟨z, (realizes i (by omega) z).mpr yes⟩
  · intro c member sound
    apply defeats c member
    intro i hi z offer yes
    exact sound i hi z offer ((realizes i (by omega) z).mpr yes)

end FirstMissingCertificateLevel
