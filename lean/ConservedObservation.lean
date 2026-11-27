import Std

namespace ConservedObservation

abbrev Bits (ι : Type) := ι → Bool

def addBits (u v : Bits ι) : Bits ι := fun i => u i ^^ v i

inductive Generated (row : Bits ι → Prop) : Bits ι → Prop where
  | zero : Generated row (fun _ => false)
  | append (a : Bits ι) {v : Bits ι} : row a → Generated row v → Generated row (addBits a v)

inductive Path (edge : σ → σ → Prop) : σ → σ → Prop where
  | stop (s : σ) : Path edge s s
  | cons {s t u} : edge s t → Path edge t u → Path edge s u

def StepRow (edge : σ → σ → Prop) (observe : σ → Bits ι) (v : Bits ι) : Prop :=
  ∃ s t, edge s t ∧ v = addBits (observe s) (observe t)

theorem telescope {edge : σ → σ → Prop} (observe : σ → Bits ι)
    {s t : σ} (h : Path edge s t) :
    Generated (StepRow edge observe) (addBits (observe s) (observe t)) := by
  induction h with
  | stop s =>
    have eq : addBits (observe s) (observe s) = fun _ => false := by
      funext i
      simp [addBits]
    rw [eq]
    exact .zero
  | @cons s t u step _ ih =>
    have row : StepRow edge observe (addBits (observe s) (observe t)) :=
      ⟨s, t, step, rfl⟩
    have combine : addBits (addBits (observe s) (observe t))
        (addBits (observe t) (observe u)) = addBits (observe s) (observe u) := by
      funext i
      simp [addBits, Bool.xor_assoc]
    rw [← combine]
    exact .append _ row ih

/-- The selected coordinates, for instance the columns of a full-rank
    minor, distinguish any two vectors in the enlarged row space. -/
def SeparatesOn (ambient : Bits ι → Prop) (probe : κ → ι) : Prop :=
  ∀ u v, ambient u → ambient v → (∀ k, u (probe k) = v (probe k)) → u = v

theorem collision_from_probes {row ambient : Bits ι → Prop} {probe : κ → ι}
    (separates : SeparatesOn ambient probe) (inside : ∀ u, Generated row u → ambient u)
    {contrast : Bits ι} (allowed : ambient contrast) :
    Generated row contrast ↔
      ∃ u, Generated row u ∧ ∀ k, u (probe k) = contrast (probe k) := by
  constructor
  · intro h
    exact ⟨_, h, fun _ => rfl⟩
  · rintro ⟨u, gen, same⟩
    exact separates u contrast (inside u gen) allowed same ▸ gen

/-- If the opposite verdict has no terminal in the initialized coset,
    the verdict of any reached terminal is forced. -/
theorem verdict {edge : σ → σ → Prop} {observe : σ → Bits ι} {s t : σ}
    {terminal : σ → Bool → Prop} {reported actual : Bool}
    (reaches : Path edge s t) (halts : terminal t actual)
    (exclude : ∀ z, terminal z (!reported) →
      ¬ Generated (StepRow edge observe) (addBits (observe s) (observe z))) :
    actual = reported := by
  by_cases same : actual = reported
  · exact same
  · have flipped : actual = !reported := by cases actual <;> cases reported <;> simp_all
    exact False.elim (exclude t (flipped ▸ halts) (telescope observe reaches))

/-- A contrast set missing a nonzero point of its span has two members
    whose nonzero sum is absent. This supplies the projection direction. -/
theorem missing_sum {member : Bits ι → Prop} {v : Bits ι}
    (gen : Generated member v) (nonzero : v ≠ fun _ => false) (missing : ¬ member v) :
    ∃ a b, member a ∧ member b ∧ a ≠ b ∧ ¬ member (addBits a b) := by
  classical
  by_cases found : ∃ a b, member a ∧ member b ∧ a ≠ b ∧ ¬ member (addBits a b)
  · exact found
  · have closed {u : Bits ι} (hu : Generated member u) : u = (fun _ => false) ∨ member u := by
      induction hu with
      | zero => exact Or.inl rfl
      | @append a u ha _ ih =>
        rcases ih with zr | mem
        · subst u
          have eq : addBits a (fun _ => false) = a := by funext i; simp [addBits]
          exact Or.inr (eq.symm ▸ ha)
        · by_cases same : a = u
          · subst u
            exact Or.inl (by funext i; simp [addBits])
          · by_cases sum : member (addBits a u)
            · exact Or.inr sum
            · exact False.elim (found ⟨a, u, ha, mem, same, sum⟩)
    exact False.elim ((closed gen).elim nonzero missing)

/-- A family of normalized diagonal matrices covers all positions.
    Their nonconstant generators cannot share a nonzero kernel vector at
    even matrix size. Here p is that vector's parity; only the value on
    the all-ones vector is needed. -/
theorem diagonal_cover_kernel {ι κ : Type} (d : ι → κ → Bool) (offset : κ → Bool)
    (covered : ∀ i, ∃ j, d i j = true) (z : ι → Bool) (p : Bool)
    (evenOnes : (∀ i, z i = true) → p = false)
    (kernel : ∀ i j, (z i && d i j) = (p && offset j)) :
    ∀ i, z i = false := by
  by_cases active : ∃ j, (p && offset j) = true
  · obtain ⟨j, hot⟩ := active
    have ones (i : ι) : z i = true := by
      have h := (kernel i j).trans hot
      cases eq : z i <;> simp_all
    rw [evenOnes ones] at hot
    contradiction
  · intro i
    obtain ⟨j, hot⟩ := covered i
    have h := kernel i j
    cases eq : z i <;> simp_all

end ConservedObservation
