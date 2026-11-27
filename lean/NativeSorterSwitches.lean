import Std

namespace NativeSorterSwitches

structure Four (α : Type) where
  a : α
  b : α
  c : α
  d : α
  deriving DecidableEq, Repr

def swapIf {α} (s : Bool) (a b : α) : α × α := if s then (b,a) else (a,b)

def layerOne {α} (s t : Bool) (x : Four α) : Four α :=
  let p := swapIf s x.a x.b
  let q := swapIf t x.c x.d
  ⟨p.1, p.2, q.1, q.2⟩

def mergeFour {α} (middle final : α → α → α × α) (x : Four α) : Four α :=
  let u := middle x.a x.c
  let v := middle x.b x.d
  let p := final u.1 v.1
  let q := final u.2 v.2
  ⟨p.1, p.2, q.1, q.2⟩

/-- The two middle comparators agree; the last pairwise comparators erase a
    reversal of their input order. No assumption on the incoming data. -/
theorem flip_pair {α} (m f : α → α → α × α) (sym : ∀ a b, f a b = f b a)
    (x : Four α) (s t : Bool) :
    mergeFour m f (layerOne (!s) (!t) x) = mergeFour m f (layerOne s t x) := by
  cases s <;> cases t <;> simp [layerOne, swapIf, mergeFour, sym]

/-- Arbitrary prescriptions on one first-layer switch per disjoint block
    extend without changing any output record of any block. -/
theorem prescribe {α I : Type} (m f : I → α → α → α × α)
    (sym : ∀ i a b, f i a b = f i b a) (x : I → Four α) (s t want : I → Bool) :
    ∃ partner : I → Bool, ∀ i, mergeFour (m i) (f i) (layerOne (want i) (partner i) (x i)) =
      mergeFour (m i) (f i) (layerOne (s i) (t i) (x i)) := by
  refine ⟨fun i => if want i = s i then t i else !(t i), fun i => ?_⟩
  by_cases h : want i = s i
  · simp [h]
  · have h' : want i = !(s i) := by cases e : want i <;> cases d : s i <;> simp_all
    simp only [if_neg h]
    rw [h']
    exact flip_pair (m i) (f i) (sym i) (x i) (s i) (t i)

/-- Simultaneous flips preserve the pair parity; this is the only invariant
    of the action on a single pair of Boolean switch settings. -/
theorem parity_orbits : ∀ s t a b : Bool,
    (Bool.xor s t = Bool.xor a b) ↔
      (s = a ∧ t = b) ∨ ((!s) = a ∧ (!t) = b) := by decide

private def asc (a b : Nat) := (min a b, max a b)

/-- On this interleaved input, changing just one honest first-layer decision
    never preserves the sorted block. -/
theorem interleaved : ∀ s t : Bool,
    (mergeFour asc asc (layerOne s t ⟨0,3,1,2⟩) = ⟨0,1,2,3⟩) ↔ s ≠ t := by decide

end NativeSorterSwitches
