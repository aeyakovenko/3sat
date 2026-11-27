import Std

namespace CertifiedReadReplies

private theorem nodup_ofFn {α : Type} {n : Nat} (f : Fin n → α)
    (inj : ∀ a b, f a = f b → a = b) : (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.nodup_cons]
    constructor
    · intro h
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
      have same := inj _ _ hi
      have values := congrArg Fin.val same
      simp at values
    · exact ih (fun i => f i.succ) (fun a b eq => by
        have same := congrArg Fin.val (inj a.succ b.succ eq)
        apply Fin.ext
        simpa using same)

private theorem length_of_nodup_subset {α : Type} [DecidableEq α] (a b : List α)
    (nd : a.Nodup) (sub : ∀ x ∈ a, x ∈ b) : a.length ≤ b.length := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp nd
    have xb := sub x (by simp)
    have smaller := ih (b.erase x) tail (fun y hy => by
      have diff : y ≠ x := by rintro rfl; exact fresh hy
      exact (List.mem_erase_of_ne diff).mpr (sub y (by simp [hy])))
    have positive := List.length_pos_of_mem xb
    rw [List.length_erase_of_mem xb] at smaller
    simp only [List.length_cons]
    omega

/-- Finite injective endomaps hit every target; no promise about a supplied
    inverse program or a procedure deciding injectivity is needed. -/
theorem hits_of_injective {n : Nat} (f : Fin n → Fin n)
    (inj : ∀ a b, f a = f b → a = b) (t : Fin n) : ∃ a, f a = t := by
  classical
  apply Classical.byContradiction
  intro none
  have nt : t ∉ List.ofFn f := fun h => none (List.mem_ofFn.mp h)
  have nd := (List.nodup_cons).mpr ⟨nt, nodup_ofFn f inj⟩
  have bound := length_of_nodup_subset (t :: List.ofFn f) (List.finRange n) nd
    (fun x _ => by exact List.mem_ofFn.mpr ⟨x, rfl⟩)
  simp at bound
  omega

/-- A verifier can check a preimage at the proposed reply. Its alternative
    certifies that the default reply is permitted by an explicit collision. -/
def certified {n : Nat} (f : Fin n → Fin n) (target fallback reply : Fin n) : Prop :=
  f reply = target ∨
  (reply = fallback ∧ ∃ a b, a ≠ b ∧ f a = f b)

theorem certified_total {n : Nat} (f : Fin n → Fin n) (target fallback : Fin n) :
    ∃ reply, certified f target fallback reply := by
  classical
  by_cases bad : ∃ a b, a ≠ b ∧ f a = f b
  · exact ⟨fallback, Or.inr ⟨rfl, bad⟩⟩
  · have inj : ∀ a b, f a = f b → a = b := by
      intro a b same
      exact Classical.byContradiction (fun different => bad ⟨a,b,different,same⟩)
    obtain ⟨a, h⟩ := hits_of_injective f inj target
    exact ⟨a, Or.inl h⟩

theorem certified_unique_if_injective {n : Nat} (f : Fin n → Fin n)
    (inj : ∀ a b, f a = f b → a=b) (target fallback : Fin n) :
    ∃ inverse, f inverse = target ∧ ∀ reply, certified f target fallback reply ↔ reply=inverse := by
  obtain ⟨a, ha⟩ := hits_of_injective f inj target
  refine ⟨a, ha, fun reply => ⟨?_, ?_⟩⟩
  · rintro (actual | ⟨_, left, right, distinct, same⟩)
    · exact inj _ _ (actual.trans ha.symm)
    · exact False.elim (distinct (inj left right same))
  · rintro rfl
    exact Or.inl ha

/-- Each block may have many private certificates with the same realized
    native log. Totality and agreement give a unique tuple of native logs. -/
theorem unique_realized_development {Block Certificate Native : Type}
    (valid : Block → Certificate → Prop) (realize : Block → Certificate → Native)
    (total : ∀ i, ∃ c, valid i c)
    (agree : ∀ i a b, valid i a → valid i b → realize i a = realize i b) :
    ∃ dev : Block → Native,
      (∀ i, ∃ c, valid i c ∧ realize i c = dev i) ∧
      ∀ other : Block → Native, (∀ i, ∃ c, valid i c ∧ realize i c = other i) → other=dev := by
  classical
  let witness := fun i => Classical.choose (total i)
  have good (i : Block) : valid i (witness i) := Classical.choose_spec (total i)
  refine ⟨fun i => realize i (witness i), fun i => ⟨witness i, good i, rfl⟩, ?_⟩
  intro other possible
  funext i
  obtain ⟨c, hc, observed⟩ := possible i
  exact observed.symm.trans (agree i c (witness i) hc (good i))

end CertifiedReadReplies
