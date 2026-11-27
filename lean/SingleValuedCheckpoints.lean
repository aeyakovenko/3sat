import Std

namespace SingleValuedCheckpoints

/-- A possibly multivalued relation contributes one output only when exactly
    that output survives. -/
def Only {α : Type} (outputs : α → Prop) (x : α) : Prop :=
  outputs x ∧ ∀ y, outputs y → y = x

theorem only_functional {α : Type} {outputs : α → Prop} {x y : α}
    (hx : Only outputs x) (hy : Only outputs y) : x = y :=
  hy.2 x hx.1

/-- If a globally single-valued program retains one successful path, the
    restricted program retains its unique output. -/
theorem retained_success {α : Type} {full capped : α → Prop} {x : α}
    (genuine : Only full x) (sound : ∀ y, capped y → full y)
    (survives : capped x) : Only capped x :=
  ⟨survives, fun y hy => genuine.2 y (sound y hy)⟩

theorem omission_excludes_each_success
    {Program Output Path : Type} (run : Program → Output → Path → Prop)
    (cheap : Program → Path → Prop) (p : Program) (x : Output)
    (missing : ¬ ∃ q, Only (fun y => ∃ w, run q y w ∧ cheap q w) x)
    (genuine : Only (fun y => ∃ w, run p y w) x) :
    ∀ w, run p x w → ¬ cheap p w := by
  intro w hw hc
  apply missing
  refine ⟨p, retained_success genuine ?_ ⟨w, hw, hc⟩⟩
  rintro y ⟨v, hv, _⟩
  exact ⟨v, hv⟩

/-- At fixed prefix width b, each empty-of-holes prefix costs every one
    of its extensions in the covered output budget. -/
theorem bad_prefix_count (bad width covered : Nat) (positive : 0 < width)
    (paid : bad * width ≤ covered) : bad ≤ covered / width :=
  (Nat.le_div_iff_mul_le positive).2 paid

end SingleValuedCheckpoints
