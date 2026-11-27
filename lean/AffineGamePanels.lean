import Std

namespace AffineGamePanels

/-- Ternary affine closure. For F₂ vectors, blend is x XOR y XOR z. -/
inductive Hull {V : Type} (blend : V → V → V → V) (generates : V → Prop) : V → Prop where
  | point {v} : generates v → Hull blend generates v
  | triple {x y z} : Hull blend generates x → Hull blend generates y →
      Hull blend generates z → Hull blend generates (blend x y z)

theorem hull_within {V : Type} {blend : V → V → V → V} {generates row : V → Prop}
    (points : ∀ v, generates v → row v)
    (closed : ∀ x y z, row x → row y → row z → row (blend x y z))
    {v} (h : Hull blend generates v) : row v := by
  induction h with
  | point hv => exact points _ hv
  | triple _ _ _ hx hy hz => exact closed _ _ _ hx hy hz

/-- Omitting each row gives a witness. In an incompatible closed family no
    witness can be in the affine hull of the other witnesses. -/
theorem independent_omission_witnesses {I V : Type} (blend : V → V → V → V)
    (rows : I → V → Prop) (p : I → V)
    (closed : ∀ i x y z, rows i x → rows i y → rows i z → rows i (blend x y z))
    (outside : ∀ i j, i ≠ j → rows j (p i))
    (incompatible : ¬ ∃ v, ∀ i, rows i v) (i : I) :
    ¬ Hull blend (fun v => ∃ j, j ≠ i ∧ p j = v) (p i) := by
  intro generated
  have own : rows i (p i) := hull_within (fun _ ⟨j, ne, eq⟩ => eq ▸ outside j i ne)
    (closed i) generated
  apply incompatible
  refine ⟨p i, ?_⟩
  intro j
  by_cases same : i = j
  · exact same ▸ own
  · exact outside i j same

/-- Each retained row needs some admissible full answer agreeing with the
    same response on every retained coordinate. -/
def Feasible {I Q : Type} (rows : I → (Q → Bool) → Prop)
    (takeRow : I → Prop) (takeCol : Q → Prop) : Prop :=
  ∃ response : Q → Bool, ∀ i, takeRow i → ∃ x, rows i x ∧
    ∀ q, takeCol q → x q = response q

/-- Injectivity of the retained coordinates on the union suffices to
    preserve incompatibility of nonempty row families. -/
theorem injective_projection {I Q : Type} (anchor : I) (rows : I → (Q → Bool) → Prop)
    (takeCol : Q → Prop)
    (separates : ∀ x y, (∃ i, rows i x) → (∃ i, rows i y) →
      (∀ q, takeCol q → x q = y q) → x = y) :
    Feasible rows (fun _ => True) takeCol ↔ ∃ x, ∀ i, rows i x := by
  constructor
  · rintro ⟨_, responses⟩
    obtain ⟨p, hp, agrees⟩ := responses anchor trivial
    refine ⟨p, ?_⟩
    intro i
    obtain ⟨v, hv, consistent⟩ := responses i trivial
    have same := separates v p ⟨i, hv⟩ ⟨anchor, hp⟩
      (fun q retained => (consistent q retained).trans (agrees q retained).symm)
    exact same ▸ hv
  · rintro ⟨v, common⟩
    exact ⟨v, fun i _ => ⟨v, common i, fun _ _ => rfl⟩⟩

theorem delete_row {I Q : Type} (rows : I → (Q → Bool) → Prop)
    (takeRow : I → Prop) (takeCol : Q → Prop) (i : I) (missing : ¬takeRow i)
    (p : Q → Bool) (outside : ∀ j, i ≠ j → rows j p) :
    Feasible rows takeRow takeCol := by
  refine ⟨p, ?_⟩
  intro j kept
  exact ⟨p, outside j (fun eq => missing (eq ▸ kept)), fun _ _ => rfl⟩

/-- A change along a single coordinate repairs row i while keeping p a
    full witness for the other rows. This also covers deleting more rows
    or coordinates at the same time. -/
theorem delete_coordinate {I Q : Type} (rows : I → (Q → Bool) → Prop)
    (takeRow : I → Prop) (takeCol : Q → Prop) (k : Q) (missing : ¬takeCol k)
    (i : I) (p alt : Q → Bool) (outside : ∀ j, i ≠ j → rows j p)
    (repair : rows i alt) (edge : ∀ q, q ≠ k → alt q = p q) :
    Feasible rows takeRow takeCol := by
  refine ⟨p, ?_⟩
  intro j _
  by_cases same : i = j
  · subst j
    exact ⟨alt, repair, fun q kept => edge q (fun eq => missing (eq ▸ kept))⟩
  · exact ⟨p, outside j same, fun _ _ => rfl⟩

/-- Reading the coefficient coordinates of a unit direction gives the
    edge condition in delete_coordinate. -/
theorem unit_edge {Q : Type} [DecidableEq Q] (k : Q) (p alt : Q → Bool)
    (diff : ∀ q, (alt q ^^ p q) = decide (q = k)) :
    ∀ q, q ≠ k → alt q = p q := by
  intro q ne
  have h := diff q
  simp [ne] at h
  exact h

end AffineGamePanels
