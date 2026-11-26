import Std

namespace ErasedSatCertificates

def Clears (pins values : I → Bool) := ∀ i, pins i = true → values i = false

def Good (a b : I → Bool) := ∀ i, ¬ (a i = true ∧ b i = true)

def Full (a b : I → Bool) := ∀ i, a i = true ∨ b i = true

/-- Universal correctness of the chosen face at the all-zero anchor.
    The parameter F includes any remaining existential witness quantifier. -/
def Cert (F : (I → Bool) → Z → Prop) (l r : I → Bool) (remaining : Z → Prop) :=
  ∀ a b z, Clears l a → Clears r b → remaining z → Good a b ∧ (Full a b → F b z)

def cost (ids : List I) (l r : I → Bool) :=
  (ids.map (fun i => (l i).toNat + (r i).toNat)).sum

theorem must_hit [DecidableEq I] {F : (I → Bool) → Z → Prop} {l r : I → Bool}
    {remaining : Z → Prop} (cert : Cert F l r remaining) (z : Z) (hz : remaining z) (i : I) :
    l i = true ∨ r i = true := by
  apply Classical.byContradiction
  intro h
  have hl : l i = false := by cases hp : l i <;> simp_all
  have hr : r i = false := by cases hp : r i <;> simp_all
  let spike := fun j => decide (j = i)
  have clearL : Clears l spike := by
    intro j hj
    by_cases he : j = i <;> simp_all [spike]
  have clearR : Clears r spike := by
    intro j hj
    by_cases he : j = i <;> simp_all [spike]
  exact (cert spike spike z clearL clearR hz).1 i ⟨by simp [spike], by simp [spike]⟩

private theorem cost_bounds (ids : List I) (l r : I → Bool)
    (hit : ∀ i, l i = true ∨ r i = true) :
    ids.length ≤ cost ids l r ∧
    (cost ids l r ≤ ids.length → ∀ i ∈ ids, (l i).toNat + (r i).toNat = 1) := by
  induction ids with
  | nil => simp [cost]
  | cons i tail ih =>
    have h : 1 ≤ (l i).toNat + (r i).toNat := by
      have hpair := hit i
      cases hl : l i <;> cases hr : r i <;> simp_all
    simp only [cost, List.map_cons, List.sum_cons, List.length_cons] at *
    constructor
    · omega
    · intro bound j mem
      rcases List.mem_cons.mp mem with eq | mem
      · subst j
        omega
      · exact ih.2 (by omega) j mem

theorem extract_winner [DecidableEq I] (ids : List I) (allIds : ∀ i, i ∈ ids)
    {F : (I → Bool) → Z → Prop} {l r : I → Bool} {remaining : Z → Prop}
    {other : Nat} (free : other = 0 → ∀ z, remaining z) (z₀ : Z) (hz : remaining z₀)
    (cert : Cert F l r remaining) (budget : cost ids l r + other ≤ ids.length) :
    other = 0 ∧ ∀ z, F l z := by
  have hit := must_hit cert z₀ hz
  obtain ⟨lo,exactly⟩ := cost_bounds ids l r hit
  have none : other = 0 := by omega
  refine ⟨none, fun z => ?_⟩
  let a := fun i => !(l i)
  have clearL : Clears l a := by intro i h; simp [a,h]
  have clearR : Clears r l := by
    intro i h
    have hu := exactly (by omega) i (allIds i)
    cases he : l i <;> simp_all
  have ful : Full a l := by intro i; cases he : l i <;> simp [a,he]
  exact (cert a l z clearL clearR (free none z)).2 ful

theorem winner_certificate {F : (I → Bool) → Z → Prop} (u : I → Bool) (win : ∀ z, F u z)
    (ids : List I) :
    Cert F u (fun i => !(u i)) (fun _ => True) ∧
      cost ids u (fun i => !(u i)) = ids.length := by
  constructor
  · intro a b z cl cr _
    constructor
    · intro i both
      cases hu : u i with
      | false => have := cr i (by simp [hu]); simp_all
      | true => have := cl i hu; simp_all
    · intro full
      have eq : b = u := by
        funext i
        rcases full i with ha | hb
        · cases hu : u i with
          | false => exact cr i (by simp [hu])
          | true => have := cl i hu; simp_all
        · cases hu : u i with
          | false => have := cr i (by simp [hu]); simp_all
          | true => exact hb
      rw [eq]
      exact win z
  · induction ids with
    | nil => rfl
    | cons i tail ih =>
      cases hu : u i <;> simp_all [cost, Nat.add_comm]

theorem spare_pin_certificate [DecidableEq I] {F : (I → Bool) → Z → Prop} (pivot : I) :
    Cert F (fun _ => true) (fun i => decide (i = pivot)) (fun _ => True) := by
  intro a b z cl cr _
  constructor
  · intro i both
    have := cl i rfl
    simp_all
  · intro full
    have ha := cl pivot rfl
    have hb := cr pivot (by simp)
    rcases full pivot with h | h <;> simp_all

/-- In the expanded physical cube, a rejection flag has precedence. -/
def Expanded (F : X → Prop) (x : X) (reject accept : I → Bool) :=
  (∀ i, reject i = false) ∧ ((∃ i, accept i = true) ∨ F x)

def ExpandedCert (desired : Bool) (data : X → Prop) (rp ap : I → Bool) (F : X → Prop) :=
  ∀ x (reject accept : I → Bool), data x → Clears rp reject → Clears ap accept →
    (Expanded F x reject accept ↔ desired = true)

private theorem clears_zero (pins : I → Bool) : Clears pins (fun _ => false) :=
  fun _ _ => rfl

private theorem clears_spike [DecidableEq I] {pins : I → Bool} {i : I} (h : pins i = false) :
    Clears pins (fun j => decide (j = i)) := by
  intro j hj
  by_cases he : j = i <;> simp_all

theorem expanded_positive_iff [DecidableEq I] {F : X → Prop} {data : X → Prop}
    (rp ap : I → Bool) (x₀ : X) (d₀ : data x₀) :
    ExpandedCert true data rp ap F ↔ (∀ i, rp i = true) ∧ ∀ x, data x → F x := by
  constructor
  · intro cert
    constructor
    · intro i
      cases h : rp i with
      | true => rfl
      | false =>
        have impossible := ((cert x₀ _ _ d₀ (clears_spike h) (clears_zero ap)).mpr rfl).1 i
        simp at impossible
    · intro x hx
      rcases ((cert x _ _ hx (clears_zero rp) (clears_zero ap)).mpr rfl).2 with bad | f
      · obtain ⟨i,hi⟩ := bad
        contradiction
      · exact f
  · rintro ⟨all, core⟩ x r a hx hr _ha
    exact ⟨fun _ => rfl, fun _ => ⟨fun i => hr i (all i), Or.inr (core x hx)⟩⟩

theorem expanded_negative_iff [DecidableEq I] {F : X → Prop} {data : X → Prop}
    (rp ap : I → Bool) (x₀ : X) (d₀ : data x₀) :
    ExpandedCert false data rp ap F ↔ (∀ i, ap i = true) ∧ ∀ x, data x → ¬ F x := by
  constructor
  · intro cert
    constructor
    · intro i
      cases h : ap i with
      | true => rfl
      | false =>
        have bad := (cert x₀ _ _ d₀ (clears_zero rp) (clears_spike h)).mp
          ⟨fun _ => rfl, Or.inl ⟨i, by simp⟩⟩
        contradiction
    · intro x hx f
      have bad := (cert x _ _ hx (clears_zero rp) (clears_zero ap)).mp ⟨fun _ => rfl, Or.inr f⟩
      contradiction
  · rintro ⟨all, core⟩ x r a hx _hr ha
    constructor
    · rintro ⟨_, h⟩
      rcases h with ⟨i,hi⟩ | f
      · have := ha i (all i)
        simp_all
      · exact False.elim (core x hx f)
    · intro h
      contradiction

end ErasedSatCertificates
