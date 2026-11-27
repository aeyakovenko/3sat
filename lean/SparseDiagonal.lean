import Std

/- One-sided diagonalization on a tree of candidate guess sequences. -/
namespace SparseDiagonal

inductive Tree where
  | leaf (report branchAccepts : Bool)
  | fork (report : Bool) (left right : Tree)

def report : Tree → Bool
  | .leaf b _ | .fork b _ _ => b

def actual : Tree → Bool
  | .leaf _ a => !a
  | .fork _ l r => report l && report r

def anyBranch : Tree → Bool
  | .leaf _ a => a
  | .fork _ l r => anyBranch l || anyBranch r

def Sound : Tree → Prop
  | .leaf b a => b = true → a = false
  | .fork b l r => (b = true → report l = true ∧ report r = true) ∧ Sound l ∧ Sound r

def HasMiss : Tree → Prop
  | .leaf b a => b = false ∧ a = false
  | .fork b l r =>
    (b = false ∧ report l = true ∧ report r = true) ∨ HasMiss l ∨ HasMiss r

theorem accepted_marks_false (t : Tree) (h : Sound t) (acc : report t = true) :
    anyBranch t = false := by
  induction t with
  | leaf b a => exact h acc
  | fork b l r ihl ihr =>
    obtain ⟨forward, hl, hr⟩ := h
    obtain ⟨al, ar⟩ := forward acc
    simp [anyBranch, ihl hl al, ihr hr ar]

theorem find_miss (t : Tree) (hf : report t = false) (hn : anyBranch t = false) :
    HasMiss t := by
  induction t with
  | leaf b a => exact ⟨hf, hn⟩
  | fork b l r ihl ihr =>
    have both : anyBranch l = false ∧ anyBranch r = false := by
      simpa [anyBranch] using hn
    cases hl : report l with
    | false => exact Or.inr (Or.inl (ihl hl both.1))
    | true =>
      cases hr : report r with
      | false => exact Or.inr (Or.inr (ihr hr both.2))
      | true => exact Or.inl ⟨hf, hl, hr⟩

/-- The root fast-report is exactly existential acceptance over its guess strings.
Every branch test at a leaf is negated in the language being simulated. -/
theorem diagonal_tree (t : Tree) (sound : Sound t) (root : report t = anyBranch t) :
    report t = false ∧ HasMiss t := by
  cases h : report t with
  | true =>
    have hn := accepted_marks_false t sound h
    rw [h, hn] at root
    contradiction
  | false => exact ⟨rfl, find_miss t h (root.symm.trans h)⟩

/-- A sound one-sided certificate search misses the whole slice on which it
is the Boolean opposite of the language decision. -/
theorem diagonal_slice (accept found : Bool) (sound : found = true → accept = true)
    (opposite : accept = !found) : accept = true ∧ found = false := by
  cases found <;> simp_all

/-- The universal clock accepts on timeout. -/
def afterClock : Option Bool → Bool
  | none => true
  | some b => !b

/-- Certifying the old machine's language allows the old detector prefix to be
patched for every length, even before the universal simulation always halts. -/
theorem old_prefix_safe (halted : Option Bool) (found old : Bool)
    (faithful : halted = some true → found = true)
    (sound : found = true → old = true)
    (known : old = afterClock halted) : old = true := by
  cases halted with
  | none => simpa [afterClock] using known
  | some b =>
    cases b with
    | false => simpa [afterClock] using known
    | true => exact sound (faithful rfl)

/-- An immediate self-patch has an easy certificate and differs from the
time-limited diagonal language when its detector has time to finish. -/
theorem easy_self_patch_fails (patched found : Bool) (easy : patched = true)
    (completeHere : patched = true → found = true) :
    patched ≠ afterClock (some found) := by
  simp [easy, completeHere easy, afterClock]

end SparseDiagonal
