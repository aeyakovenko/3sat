import Std

namespace RareSelectorPruning

inductive Op (ι σ : Type) where
  | halt (answer : Bool)
  | probe (site : ι) (next : Bool → σ)

variable {ι σ : Type} (bits : ι → Bool)

/-- The list contains precisely the tested vertices, including repetitions. -/
inductive Run (P : σ → Op ι σ) : σ → List σ → Bool → Prop where
  | halt (h : P s = .halt b) : Run P s [] b
  | probe (h : P s = .probe i k) (tail : Run P (k (bits i)) l b) :
      Run P s (s :: l) b

def cut (P : σ → Op ι σ) (keep : σ → Bool) (target : Bool) (s : σ) : Op ι σ :=
  match P s with
  | .halt b => .halt b
  | .probe i k => if keep s then .probe i k else .halt (!target)

theorem retained {P : σ → Op ι σ} {keep : σ → Bool} {target : Bool}
    {s : σ} {l : List σ} {v : Bool} (h : Run bits P s l v)
    (saved : ∀ q ∈ l, keep q = true) : Run bits (cut P keep target) s l v := by
  induction h with
  | halt hr => exact .halt (by simp [cut, hr])
  | @probe s i k l b hp tail ih =>
    apply Run.probe (i := i) (k := k)
    · simp [cut, hp, saved s (by simp)]
    · exact ih (fun q hq => saved q (by simp [hq]))

theorem sound_at_target {P : σ → Op ι σ} {keep : σ → Bool} {target : Bool}
    {s : σ} {l : List σ} {v : Bool} (h : Run bits (cut P keep target) s l v)
    (hv : v = target) : Run bits P s l v := by
  induction h with
  | @halt s b hr =>
    cases he : P s with
    | halt z =>
      have : z = b := by simpa [cut, he] using hr
      exact .halt (this ▸ he)
    | probe i k =>
      cases hk : keep s <;> simp [cut, he, hk, hv] at hr
  | @probe s i k l b hp tail ih =>
    cases he : P s with
    | halt z => simp [cut, he] at hp
    | probe j f =>
      cases hk : keep s
      · simp [cut, he, hk] at hp
      · have pair : j = i ∧ f = k := by simpa [cut, he, hk] using hp
        obtain ⟨rfl, rfl⟩ := pair
        exact .probe he (ih hv)

end RareSelectorPruning
