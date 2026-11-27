import Std

namespace CoherentLiteralPrefixes

/-- Read the bits of a candidate tuple from low to high. Lists store the
    most recently revealed bit at the front. -/
def viableTo (ok : List Bool → Prop) (node : List Bool) : Nat → Prop
  | 0 => ok node
  | n+1 => ok node ∧
      (viableTo ok (false :: node) n ∨ viableTo ok (true :: node) n)

def unbounded (ok : List Bool → Prop) (node : List Bool) : Prop :=
  ∀ n, viableTo ok node n

private theorem dropLast {ok : List Bool → Prop} (n : Nat) (node : List Bool)
    (h : viableTo ok node (n+1)) : viableTo ok node n := by
  induction n generalizing node with
  | zero => exact h.1
  | succ n ih =>
    obtain ⟨here, next⟩ := h
    exact ⟨here, next.elim (fun h => Or.inl (ih _ h)) (fun h => Or.inr (ih _ h))⟩

private theorem truncate {ok : List Bool → Prop} {node : List Bool} {m n : Nat}
    (le : m ≤ n) (h : viableTo ok node n) : viableTo ok node m := by
  induction le with
  | refl => exact h
  | step _ ih => exact ih (dropLast _ _ h)

private theorem infiniteChild {ok : List Bool → Prop} {node : List Bool}
    (h : unbounded ok node) :
    unbounded ok (false :: node) ∨ unbounded ok (true :: node) := by
  classical
  by_cases left : unbounded ok (false :: node)
  · exact Or.inl left
  · right
    unfold unbounded at left ⊢
    have someFail : ∃ n, ¬ viableTo ok (false :: node) n := Classical.not_forall.mp left
    obtain ⟨n, fail⟩ := someFail
    intro m
    have next := (h (max n m + 1)).2
    exact next.elim (fun hl => (fail (truncate (Nat.le_max_left _ _) hl)).elim)
      (fun hr => truncate (Nat.le_max_right _ _) hr)

private noncomputable def pick (ok : List Bool → Prop) (node : List Bool) : Bool := by
  classical
  exact if unbounded ok (false :: node) then false else true

private theorem pickGood {ok : List Bool → Prop} {node : List Bool}
    (h : unbounded ok node) : unbounded ok (pick ok node :: node) := by
  classical
  by_cases hl : unbounded ok (false :: node)
  · simp [pick, hl]
  · simpa [pick, hl] using (infiniteChild h).resolve_left hl

private noncomputable def states (ok : List Bool → Prop) : Nat → List Bool
  | 0 => []
  | j+1 => pick ok (states ok j) :: states ok j

def bitPrefix (bits : Nat → Bool) : Nat → List Bool
  | 0 => []
  | j+1 => bits j :: bitPrefix bits j

/-- A coherent infinite bit assignment passes every test triggered at a
    finite precision iff every precision admits a passing full path. -/
theorem coherent_iff (ok : List Bool → Prop) :
    unbounded ok [] ↔ ∃ bits : Nat → Bool, ∀ j, ok (bitPrefix bits j) := by
  constructor
  · intro h
    let bits := fun j => pick ok (states ok j)
    have eqPrefix (j : Nat) : bitPrefix bits j = states ok j := by
      induction j with
      | zero => rfl
      | succ j ih => simp [bitPrefix, states, bits, ih]
    have keeps (j : Nat) : unbounded ok (states ok j) := by
      induction j with
      | zero => exact h
      | succ j ih => exact pickGood ih
    exact ⟨bits, fun j => eqPrefix j ▸ keeps j 0⟩
  · rintro ⟨bits, valid⟩
    have fromNode (k j : Nat) : viableTo ok (bitPrefix bits j) k := by
      induction k generalizing j with
      | zero => exact valid j
      | succ k ih =>
        refine ⟨valid j, ?_⟩
        have child := ih (j+1)
        cases h : bits j with
        | false => exact Or.inl (by simpa [bitPrefix, h] using child)
        | true => exact Or.inr (by simpa [bitPrefix, h] using child)
    exact fun k => fromNode k 0

end CoherentLiteralPrefixes

namespace VerifiedAssignmentSearch

/-- The suffix of a Boolean assignment still to be chosen has this length.
    The decidable predicate evaluates a completed assignment. -/
def hasCompletion (eval : List Bool → Bool) (chosen : List Bool) : Nat → Bool
  | 0 => eval chosen
  | n+1 => hasCompletion eval (false :: chosen) n || hasCompletion eval (true :: chosen) n

abbrev Candidate := List Bool → Nat → Bool

def recover (ask : Candidate) (chosen : List Bool) : Nat → List Bool
  | 0 => chosen
  | n+1 =>
    if ask (false :: chosen) n then recover ask (false :: chosen) n
    else recover ask (true :: chosen) n

private theorem verification_sound (eval : List Bool → Bool) (ask : Candidate)
    (n : Nat) (chosen : List Bool)
    (verified : eval (recover ask chosen n) = true) : hasCompletion eval chosen n = true := by
  induction n generalizing chosen with
  | zero => exact verified
  | succ n ih =>
    cases h : ask (false :: chosen) n with
    | false =>
      have smaller := ih (true :: chosen) (by simpa [recover, h] using verified)
      simp [hasCompletion, smaller]
    | true =>
      have smaller := ih (false :: chosen) (by simpa [recover, h] using verified)
      simp [hasCompletion, smaller]

private theorem truthful_recovers (eval : List Bool → Bool) (ask : Candidate)
    (total : Nat)
    (truthful : ∀ node n, node.length + n = total → ask node n = hasCompletion eval node n)
    (n : Nat) (chosen : List Bool) (size : chosen.length + n = total)
    (existsModel : hasCompletion eval chosen n = true) :
    eval (recover ask chosen n) = true := by
  induction n generalizing chosen with
  | zero => exact existsModel
  | succ n ih =>
    have sizeF : (false :: chosen).length + n = total := by simp at *; omega
    have sizeT : (true :: chosen).length + n = total := by simp at *; omega
    have reply := truthful (false :: chosen) n sizeF
    cases h : hasCompletion eval (false :: chosen) n with
    | false =>
      have right : hasCompletion eval (true :: chosen) n = true := by
        simpa [hasCompletion, h] using existsModel
      simpa [recover, reply, h] using ih (true :: chosen) sizeT right
    | true => simpa [recover, reply, h] using ih (false :: chosen) sizeF h

/-- Trying every oracle and accepting only a verified assignment is sound
    for arbitrary candidates and complete when the list contains one
    oracle correct on all restrictions. -/
theorem verified_list_decides (eval : List Bool → Bool) (candidates : List Candidate)
    (n : Nat) (containsCorrect : ∃ ask ∈ candidates, ∀ node k,
      node.length + k = n → ask node k = hasCompletion eval node k) :
    (candidates.any (fun ask => eval (recover ask [] n)) = true) ↔
    hasCompletion eval [] n = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨ask, _, verified⟩
    exact verification_sound eval ask n [] verified
  · intro existsModel
    obtain ⟨ask, mem, truthful⟩ := containsCorrect
    exact ⟨ask, mem, truthful_recovers eval ask n truthful n [] (by simp) existsModel⟩

/-- All four choices of dummy signs reduce exactly to the pinned literal. -/
theorem four_pinning_clauses (lit u v : Bool) :
    ((lit || u || v) && (lit || u || !v) &&
      (lit || !u || v) && (lit || !u || !v)) = lit := by
  cases lit <;> cases u <;> cases v <;> decide

end VerifiedAssignmentSearch
