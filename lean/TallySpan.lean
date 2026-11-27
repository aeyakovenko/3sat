import Std

namespace TallySpan

abbrev Vector (ι : Type) := ι → Bool

def plus (u v : Vector ι) : Vector ι := fun j => u j ^^ v j

inductive Span (pool : Vector ι → Prop) : Vector ι → Prop where
  | zero : Span pool (fun _ => false)
  | add {u v} : pool u → Span pool v → Span pool (plus u v)

theorem annihilates_span {pool : Vector ι → Prop} (atTail : Vector ι → Bool)
    (zero : atTail (fun _ => false) = false)
    (linear : ∀ u v, atTail (plus u v) = (atTail u ^^ atTail v))
    (valid : ∀ v, pool v → atTail v = false) {v} (gen : Span pool v) :
    atTail v = false := by
  induction gen with
  | zero => exact zero
  | add hu _ ih => rw [linear, valid _ hu, ih]; rfl

def Projected (proposed : κ → Prop) (project : κ → Vector ι) (v : Vector ι) : Prop :=
  ∃ claim, proposed claim ∧ project claim = v

/-- The new verifier can accept original claims with an aliased projection. -/
theorem lifting {proposed correct : κ → Prop} (project : κ → Vector ι)
    (atTail : Vector ι → Bool) (zero : atTail (fun _ => false) = false)
    (linear : ∀ u v, atTail (plus u v) = (atTail u ^^ atTail v))
    (tailExact : ∀ claim, correct claim ↔ atTail (project claim) = false)
    (sound : ∀ claim, proposed claim → correct claim) :
    (∀ claim, proposed claim → Span (Projected proposed project) (project claim)) ∧
    (∀ claim, Span (Projected proposed project) (project claim) → correct claim) := by
  constructor
  · intro claim accepted
    have h := Span.add (pool := Projected proposed project)
      (u := project claim) ⟨claim, accepted, rfl⟩ Span.zero
    have e : plus (project claim) (fun _ => false) = project claim := by
      funext i; simp [plus]
    exact e ▸ h
  · intro claim generated
    apply (tailExact claim).2
    apply annihilates_span atTail zero linear _ generated
    rintro v ⟨c, hc, rfl⟩
    exact (tailExact c).1 (sound c hc)

def parityAt {σ : Type} : List (σ → Bool) → σ → Bool
  | [], _ => false
  | r :: rs, x => r x ^^ parityAt rs x

theorem parity_agrees {σ : Type} (rows : List (σ → Bool)) (s t : σ)
    (agree : ∀ r ∈ rows, r s = r t) : parityAt rows s = parityAt rows t := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    have eq := agree r (by simp)
    simp only [parityAt, eq]
    exact congrArg (fun b => r t ^^ b) (ih (fun u hu => agree u (by simp [hu])))

/-- Simultaneous realization of every selected row on the tail preserves
    whether their XOR is identically zero. Apply also to each subfamily. -/
theorem dependence_iff {σ τ : Type} (rows : List (σ → Bool)) (embed : τ → σ)
    (realizes : ∀ x, ∃ t, ∀ r ∈ rows, r x = r (embed t)) :
    (∀ x, parityAt rows x = false) ↔ (∀ t, parityAt rows (embed t) = false) := by
  constructor
  · exact fun all t => all (embed t)
  · intro restricted x
    obtain ⟨t, same⟩ := realizes x
    exact (parity_agrees rows x (embed t) same).trans (restricted t)

/-- Once the rank is known, any guessed basis gives the canonical bit. -/
theorem canonical_bit {basis : β → Prop} (bit : β → Bool) (value : Bool)
    (existsBasis : ∃ b, basis b) (uniqueOutput : ∀ b, basis b → bit b = value) :
    (∃ b, basis b ∧ bit b = true) ↔ value = true := by
  constructor
  · rintro ⟨b, hb, h⟩
    exact (uniqueOutput b hb).symm.trans h
  · intro h
    obtain ⟨b, hb⟩ := existsBasis
    exact ⟨b, hb, (uniqueOutput b hb).trans h⟩

/-- Choosing the first sufficiently rich prefix preserves finite-length
    soundness even when erroneous certificates arrive later. -/
theorem earliest_is_sound {accepted : Nat → κ → Prop} {correct : κ → Prop}
    {rich : Nat → Prop} {first good : Nat}
    (monotone : ∀ s t, s ≤ t → ∀ c, accepted s c → accepted t c)
    (least : ∀ t, rich t → first ≤ t) (enough : rich good)
    (sound : ∀ c, accepted good c → correct c) :
    ∀ c, accepted first c → correct c :=
  fun c hc => sound c (monotone first good (least good enough) c hc)

end TallySpan
