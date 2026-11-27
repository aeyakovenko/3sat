import Std

namespace Reflection

/-- A machine runs its ordinary branch off a designated template.
    In the template it rejects only a purported proof of contradiction. -/
def patched (decode : X → Option P) (bad : P → Bool) (base : X → Bool) (x : X) : Bool :=
  match decode x with
  | none => base x
  | some p => !(bad p)

/-- Exact one-sided soundness, before any arithmetization or timing claim. -/
theorem soundness_iff
    (encode : P → X) (decode : X → Option P) (roundtrip : ∀ p, decode (encode p) = some p)
    (sat : X → Prop) (templateSat : ∀ p, sat (encode p))
    (bad : P → Bool) (base : X → Bool) :
    (∀ x, sat x → patched decode bad base x = true) ↔
      (∀ p, bad p = false) ∧ (∀ x, decode x = none → sat x → base x = true) := by
  constructor
  · intro sound
    constructor
    · intro p
      have h := sound (encode p) (templateSat p)
      cases hb : bad p <;> simp_all [patched, roundtrip]
    · intro x hx hs
      simpa [patched, hx] using sound x hs
  · rintro ⟨noBad, off⟩ x hs
    cases hx : decode x with
    | none => simpa [patched, hx] using off x hx hs
    | some p => simp [patched, hx, noBad]

/-- If all designated formulas for short alleged proofs lie within a size cap,
    soundness through the cap rules out those proofs. -/
theorem bounded_reflection
    (encode : P → X) (decode : X → Option P) (roundtrip : ∀ p, decode (encode p) = some p)
    (sat : X → Prop) (templateSat : ∀ p, sat (encode p))
    (bad : P → Bool) (base : X → Bool)
    (inputLength : X → Nat) (proofLength : P → Nat) (limit cap : Nat)
    (fits : ∀ p, proofLength p ≤ limit → inputLength (encode p) ≤ cap)
    (sound : ∀ x, inputLength x ≤ cap → sat x → patched decode bad base x = true) :
    ∀ p, proofLength p ≤ limit → bad p = false := by
  intro p hp
  have h := sound (encode p) (fits p hp) (templateSat p)
  cases hb : bad p <;> simp_all [patched, roundtrip]

/-- No input shorter than the simulated halting time becomes an error.
    The ordinary branch is a correct baseline. -/
theorem no_early_error
    (decode : X → Option Nat) (inputLength : X → Nat)
    (fits : ∀ x t, decode x = some t → t ≤ inputLength x)
    (sat : X → Bool) (templateSat : ∀ x t, decode x = some t → sat x = true)
    (haltsBy : Nat → Bool) (first : Nat)
    (early : ∀ t, t < first → haltsBy t = false)
    (x : X) (short : inputLength x < first) :
    patched decode haltsBy sat x = sat x := by
  cases h : decode x with
  | none => simp [patched, h]
  | some t =>
    have ht := Nat.lt_of_le_of_lt (fits x t h) short
    simp [patched, h, early t ht, templateSat x t h]

/-- The canonical formula for a successful simulation really is an error. -/
theorem error_on_halt
    (encode : Nat → X) (decode : X → Option Nat)
    (roundtrip : ∀ t, decode (encode t) = some t)
    (sat : X → Bool) (templateSat : ∀ t, sat (encode t) = true)
    (haltsBy : Nat → Bool) (first : Nat) (halt : haltsBy first = true) :
    patched decode haltsBy sat (encode first) ≠ sat (encode first) := by
  simp [patched, roundtrip, halt, templateSat]

end Reflection
