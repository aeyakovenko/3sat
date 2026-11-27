import Std

/- A Boolean vector is represented by its set of true coordinates. -/
namespace LocalSummary

abbrev V (ι : Type) := ι → Prop

def Sub {ι : Type} (x y : V ι) := ∀ i, x i → y i
def Compl {ι : Type} (x : V ι) : V ι := fun i => ¬x i

def Decodes {ι κ : Type} (h : V ι → V κ)
    (d : V ι → V κ → V ι) : Prop :=
  (∀ x y u v, Sub x y → Sub u v → Sub (d x u) (d y v)) ∧
  ∀ x i, d x (h x) i ↔ Compl x i

def Separates {ι κ : Type} (h : V ι → V κ) : Prop :=
  ∀ x y, Sub x y → Sub (h x) (h y) → Sub y x

theorem decoder_iff {ι κ : Type} (h : V ι → V κ) :
    (∃ d, Decodes h d) ↔ Separates h := by
  constructor
  · rintro ⟨d, mono, correct⟩ x y hxy huv i hy
    classical
    by_cases hi : x i
    · exact hi
    · have p := (correct x i).2 hi
      exact False.elim (((correct y i).1 (mono x y (h x) (h y) hxy huv i p)) hy)
  · intro sep
    let d : V ι → V κ → V ι := fun x u i =>
      ∃ t, Sub t x ∧ Sub (h t) u ∧ ¬t i
    refine ⟨d, ?_, ?_⟩
    · intro x y u v hxy huv i
      rintro ⟨t, htx, htu, hti⟩
      exact ⟨t, fun j hj => hxy j (htx j hj),
        fun j hj => huv j (htu j hj), hti⟩
    · intro x i
      constructor
      · rintro ⟨t, htx, htu, hti⟩ hi
        exact hti (sep t x htx htu i hi)
      · intro hi
        exact ⟨x, fun _ p => p, fun _ p => p, hi⟩

/-- Two permutations that agree off one slot must agree in that slot. This is
the exchange step in the saturated chain argument. -/
theorem forced_slot {I K : Type} (a b : I → K) (i : I)
    (onto : ∀ k, ∃ j, b j = k)
    (inj : ∀ u v, a u = a v → u = v)
    (other : ∀ j, j ≠ i → b j = a j) : b i = a i := by
  obtain ⟨j, hj⟩ := onto (a i)
  by_cases he : j = i
  · simpa [he] using hj
  · have hji := inj j i ((other j he).symm.trans hj)
    exact False.elim (he hji)

theorem reverse_comparator (a b : Bool) :
    ((! (a || b)) || (b && ! (a && b))) = !a ∧
    ((! (a || b)) || (a && ! (a && b))) = !b := by
  cases a <;> cases b <;> decide

end LocalSummary
