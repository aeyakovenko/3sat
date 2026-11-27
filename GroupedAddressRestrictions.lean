import Std

namespace GroupedAddressRestrictions

variable {α : Type u}

def change (clamp : α → α) (f : α → Bool) (x : α) : Bool :=
  Bool.xor (f x) (f (clamp x))

def rest (f : α → Bool) : List (α → α) → (α → Bool)
  | [] => f
  | c :: cs => rest (change c f) cs

def reconstructed (f : α → Bool) : List (α → α) → (α → Bool)
  | [] => fun _ => false
  | c :: cs => fun x => Bool.xor (f (c x)) (reconstructed (change c f) cs x)

theorem telescope (f : α → Bool) (cs : List (α → α)) (x : α) :
    Bool.xor (reconstructed f cs x) (rest f cs x) = f x := by
  induction cs generalizing f with
  | nil => cases h : f x <;> simp [reconstructed, rest, h]
  | cons c cs ih =>
    have combine (a b u v : Bool) (h : Bool.xor u v = Bool.xor a b) :
        Bool.xor (Bool.xor b u) v = a := by
      cases a <;> cases b <;> cases u <;> cases v <;> simp_all
    exact combine (f x) (f (c x)) _ _ (ih (change c f))


theorem zeroRest (cs : List (α → α)) :
    rest (fun _ => false) cs = (fun _ => false) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => exact ih

theorem missing (f : α → Bool) (cs : List (α → α)) (a : α → α)
    (member : a ∈ cs) (fixed : ∀ x, f (a x) = f x)
    (commutes : ∀ c ∈ cs, ∀ x, c (a x) = a (c x)) :
    rest f cs = fun _ => false := by
  induction cs generalizing f with
  | nil => cases member
  | cons c cs ih =>
    rcases List.mem_cons.mp member with h | h
    · subst c
      have hz : change a f = fun _ => false := by
        funext x
        simp [change, fixed]
      simp only [rest, hz]
      exact zeroRest cs
    · apply ih (change c f) h
      · intro x
        simp [change, fixed, commutes c (by simp) x]
      · intro d hd
        exact commutes d (by simp [hd])

def sumTerms : List (α → Bool) → α → Bool
  | [] => fun _ => false
  | f :: fs => fun x => Bool.xor (f x) (sumTerms fs x)

theorem restXor (cs : List (α → α)) (f g : α → Bool) :
    rest (fun x => Bool.xor (f x) (g x)) cs =
      fun x => Bool.xor (rest f cs x) (rest g cs x) := by
  induction cs generalizing f g with
  | nil => rfl
  | cons c cs ih =>
    have distribute : change c (fun x => Bool.xor (f x) (g x)) =
        fun x => Bool.xor (change c f x) (change c g x) := by
      funext x
      simp only [change]
      cases f x <;> cases g x <;> cases f (c x) <;> cases g (c x) <;> rfl
    simp only [rest, distribute, ih]

theorem exactOnSum (fs : List (α → Bool)) (cs : List (α → α))
    (absent : ∀ f ∈ fs, ∃ a ∈ cs, (∀ x, f (a x) = f x) ∧
      (∀ c ∈ cs, ∀ x, c (a x) = a (c x))) :
    reconstructed (sumTerms fs) cs = sumTerms fs := by
  have vanishes : rest (sumTerms fs) cs = fun _ => false := by
    induction fs with
    | nil => exact zeroRest cs
    | cons f fs ih =>
      obtain ⟨a, ha, fixed, commutes⟩ := absent f (by simp)
      have tail := ih (by intro g hg; exact absent g (by simp [hg]))
      simp only [sumTerms, restXor, missing f cs a ha fixed commutes, tail]
      rfl
  funext x
  have h := telescope (sumTerms fs) cs x
  simpa [vanishes] using h

#print axioms exactOnSum

end GroupedAddressRestrictions
