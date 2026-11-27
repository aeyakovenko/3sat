import Std

/-! Causal reconstruction on a family of hidden forward tables. In challenge
blocks the decoder may inspect the entire permitted part of the forward table
and every earlier true answer. The local-message tuple encodes only challenge
blocks. Unselected answers and permitted raw replies are constant on the
family. The probabilistic choice of the family and the bit bound are in prose. -/
namespace BatchedLastWriterPrefix

variable {Hidden Pos Word Answer Advice Message : Type}

structure Forecast (h : Nat) (challenge : Fin h → Prop)
    (permitted : Fin h → Pos → Prop) where
  table : Hidden → Pos → Word
  answer : Hidden → Fin h → Answer
  advice : Hidden → Advice
  message : Hidden → (j : Fin h) → challenge j → Message
  decode : (j : Fin h) → Advice → Message → (Fin j.val → Answer) →
    ({p : Pos // permitted j p} → Word) → Answer
  correct : ∀ x j (cj : challenge j), answer x j =
    decode j (advice x) (message x j cj)
      (fun i => answer x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩)
      (fun p => table x p.val)
  publicTable : ∀ x y j, challenge j → ∀ p, permitted j p → table x p = table y p
  publicAnswer : ∀ x y j, ¬challenge j → answer x j = answer y j

namespace Forecast

variable {h : Nat} {challenge : Fin h → Prop} {permitted : Fin h → Pos → Prop}
variable (F : Forecast (Hidden := Hidden) (Word := Word) (Answer := Answer)
  (Advice := Advice) (Message := Message) h challenge permitted)

def code (x : Hidden) : Advice × ({j : Fin h // challenge j} → Message) :=
  (F.advice x, fun j => F.message x j.val j.property)

theorem recover_prefix (x y : Hidden) (equalCode : F.code x = F.code y) :
    ∀ j, F.answer x j = F.answer y j := by
  have common : F.advice x = F.advice y := congrArg Prod.fst equalCode
  have messages := congrArg Prod.snd equalCode
  intro j
  have recover (n : Nat) : ∀ small : n < h, F.answer x ⟨n, small⟩ = F.answer y ⟨n, small⟩ := by
    induction n using Nat.strongRecOn with
    | ind n earlier =>
      intro small
      let j' : Fin h := ⟨n, small⟩
      by_cases cj : challenge j'
      · have localEq : F.message x j' cj = F.message y j' cj :=
          congrFun messages ⟨j', cj⟩
        have past : (fun i : Fin j'.val => F.answer x ⟨i.val, Nat.lt_trans i.isLt j'.isLt⟩) =
            (fun i : Fin j'.val => F.answer y ⟨i.val, Nat.lt_trans i.isLt j'.isLt⟩) := by
          funext i
          exact earlier i.val i.isLt _
        have raw : (fun p : {p // permitted j' p} => F.table x p.val) =
            (fun p : {p // permitted j' p} => F.table y p.val) := by
          funext p
          exact F.publicTable x y j' cj p.val p.property
        change F.answer x j' = F.answer y j'
        rw [F.correct x j' cj, F.correct y j' cj, common, localEq, past, raw]
      · exact F.publicAnswer x y j' cj
  exact recover j.val j.isLt

theorem code_injective
    (distinguish : ∀ x y, (∀ j, F.answer x j = F.answer y j) → x = y)
    (x y : Hidden) (equalCode : F.code x = F.code y) : x = y :=
  distinguish x y (F.recover_prefix x y equalCode)

end Forecast

/-! In the binary construction the occurrence index of a color is determined
by its earlier occurrences. Encoding a longer bit pattern keeps the *full*
positions of its prefix and the color sequence determines the original bits. -/
def assignColors {α : Type} (position : Bool → Nat → α) :
    Nat → Nat → List Bool → List α
  | _, _, [] => []
  | i, j, false :: xs => position false i :: assignColors position (i+1) j xs
  | i, j, true :: xs => position true j :: assignColors position i (j+1) xs

theorem assign_append {α : Type} (position : Bool → Nat → α)
    (front tail : List Bool) (i j : Nat) :
    ∃ rest, assignColors position i j (front ++ tail) =
      assignColors position i j front ++ rest := by
  induction front generalizing i j with
  | nil => exact ⟨_, rfl⟩
  | cons b bs ih =>
    cases b with
    | false =>
      obtain ⟨rest, eq⟩ := ih (i+1) j
      exact ⟨rest, congrArg (List.cons _) eq⟩
    | true =>
      obtain ⟨rest, eq⟩ := ih i (j+1)
      exact ⟨rest, congrArg (List.cons _) eq⟩

theorem recover_colors {α : Type} (position : Bool → Nat → α) (color : α → Bool)
    (colored : ∀ b n, color (position b n) = b) (bs : List Bool) (i j : Nat) :
    (assignColors position i j bs).map color = bs := by
  induction bs generalizing i j with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [assignColors, colored, ih]

/-! Four proper sign variants of one unit force its data literal at every
auxiliary assignment. The next equivalence states the SAT pin semantics
on an abstract position/variable bijection, including arbitrary anchors. -/
def properUnit (l a b : Bool) : Bool :=
  (l || a || b) && (l || !a || b) && (l || a || !b) && (l || !a || !b)

theorem proper_unit_exact (l a b : Bool) : properUnit l a b = l := by
  cases l <;> cases a <;> cases b <;> decide

theorem pinned_core_iff {Pos Name : Type} (pi : Pos → Name) (inv : Name → Pos)
    (leftInv : ∀ i, inv (pi i) = i) (rightInv : ∀ y, pi (inv y) = y)
    (isEven : Pos → Bool) (y : Name) (a b c : Bool) :
    (∃ assignment : Name → Bool,
      (∀ i, properUnit (assignment (pi i) == isEven i) a b = true) ∧
      properUnit (assignment y) a c = true) ↔ isEven (inv y) = true := by
  simp only [proper_unit_exact, beq_iff_eq]
  constructor
  · rintro ⟨assignment, core, pin⟩
    have fixed := core (inv y)
    simpa [rightInv, pin] using fixed.symm
  · intro yes
    exact ⟨fun z => isEven (inv z), fun i => by simp [leftInv], yes⟩

end BatchedLastWriterPrefix
