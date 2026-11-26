import Std

namespace AddressConsistencyCertificates

abbrev Memory := Nat → Nat
abbrev Keep := Nat → Bool

inductive Event where
  | load (address reply : Nat)
  | store (address value : Nat)
  deriving Repr

def write (mem : Memory) (a v : Nat) : Memory :=
  fun b => if b = a then v else mem b

/-- Full last-write check on the chronological candidate trace. Repetitions are
harmless when its resulting list is used as a set of addresses. -/
def faults : List Event → Memory → List Nat
  | [], _ => []
  | .store a v :: rest, mem => faults rest (write mem a v)
  | .load a v :: rest, mem =>
    if mem a = v then faults rest mem else a :: faults rest mem

/-- The concrete monitor updates only retained words and ignores all loads
elsewhere. The separate candidate predicate can enforce all native opcodes. -/
def check (keep : Keep) : List Event → Memory → Prop
  | [], _ => True
  | .store a v :: rest, slots =>
    check keep rest (if keep a then write slots a v else slots)
  | .load a v :: rest, slots =>
    (keep a = true → slots a = v) ∧ check keep rest slots

theorem checked_iff {keep : Keep} (trace : List Event) (mem slots : Memory)
    (agree : ∀ a, keep a = true → slots a = mem a) :
    check keep trace slots ↔ ∀ a ∈ faults trace mem, keep a = false := by
  induction trace generalizing mem slots with
  | nil => simp [check, faults]
  | cons event rest ih =>
    cases event with
    | store a v =>
      have nextAgree : ∀ b, keep b = true →
          (if keep a then write slots a v else slots) b = (write mem a v) b := by
        intro b hb
        by_cases same : b = a
        · subst b
          simp [hb, write]
        · cases ha : keep a <;> simp [ha, write, same, agree b hb]
      exact ih _ _ nextAgree
    | load a v =>
      cases hk : keep a <;> by_cases hv : mem a = v <;>
        simp [check, faults, ih mem slots agree, hk, hv, agree a] at *

theorem hits_iff_no_accept (candidate : List Event → Prop) (keep : Keep) :
    (∀ trace, candidate trace →
      ∃ a ∈ faults trace (fun _ => 0), keep a = true) ↔
    ¬ ∃ trace, candidate trace ∧ check keep trace (fun _ => 0) := by
  classical
  constructor
  · rintro hits ⟨trace, ht, hc⟩
    obtain ⟨a, ha, yes⟩ := hits trace ht
    have clean := (checked_iff trace (fun _ => 0) (fun _ => 0) (by simp)).mp hc
    simp [yes] at clean
    exact Bool.noConfusion ((clean a ha).symm.trans yes)
  · intro no trace ht
    apply Classical.byContradiction
    intro denied
    apply no
    refine ⟨trace, ht, (checked_iff trace (fun _ => 0) (fun _ => 0) (by simp)).mpr ?_⟩
    intro a ha
    cases h : keep a with
    | false => rfl
    | true => exact False.elim (denied ⟨a, ha, h⟩)

end AddressConsistencyCertificates
