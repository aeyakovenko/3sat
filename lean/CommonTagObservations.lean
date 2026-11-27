import Std

namespace CommonTagObservations

inductive PhysicalBit (Key : Type) where
  | fixed (value : Bool)
  | selector (key : Key) (complement : Bool)
deriving DecidableEq

def eval (s : Key → Bool) : PhysicalBit Key → Bool
  | .fixed v => v
  | .selector p c => xor (s p) c

def permits (s : Key → Bool) (o : PhysicalBit Key × Bool) :=
  eval s o.1 = o.2

def force (o : PhysicalBit Key × Bool) (p : Key) (v : Bool) : Prop :=
  ∃ b c, o = (.selector p c, b) ∧ v = xor b c

theorem extract {s : Key → Bool} {o : PhysicalBit Key × Bool} (h : permits s o)
    (f : force o p v) : s p = v := by
  rcases f with ⟨b,c,rfl,rfl⟩
  cases hs : s p <;> cases b <;> cases c <;> simp_all [permits,eval]

theorem completion (O : List (PhysicalBit Key × Bool)) :
    (∃ s : Key → Bool, ∀ o ∈ O, permits s o) ↔
    (∀ a b, (PhysicalBit.fixed a,b) ∈ O → a=b) ∧
    (∀ p, ∀ u ∈ O, ∀ v ∈ O, force u p true → force v p false → False) := by
  classical
  constructor
  · rintro ⟨s,hs⟩
    constructor
    · exact fun a b h => hs _ h
    · intro p u hu v hv h₁ h₂
      have a := extract (hs u hu) h₁
      have b := extract (hs v hv) h₂
      simp_all
  · rintro ⟨hfix, hcon⟩
    let s : Key → Bool := fun p => decide (∃ u ∈ O, force u p true)
    refine ⟨s,?_⟩
    rintro ⟨t,b⟩ hm
    cases t with
    | fixed a => exact hfix a b hm
    | selector p c =>
      have hf : force (.selector p c,b) p (xor b c) := ⟨b,c,rfl,rfl⟩
      have hv : s p = xor b c := by
        cases he : xor b c with
        | true =>
          have hhit : ∃ u ∈ O, force u p true := ⟨_,hm,he ▸ hf⟩
          exact decide_eq_true hhit
        | false =>
          have hmiss : ¬ ∃ u ∈ O, force u p true := by
            rintro ⟨u,hu,h⟩
            exact hcon p u hu _ hm h (he ▸ hf)
          exact decide_eq_false hmiss
      cases b <;> cases c <;> simp_all [permits,eval]

end CommonTagObservations
