import Std

namespace ForcedStoppingRules

abbrev Cases (α : Type) := List (List α × Bool)

def run (rule : α → Option Bool) : List α → Option Bool
  | [] => none
  | a :: tail => match rule a with
    | none => run rule tail
    | some b => some b

def front [DecidableEq α] (allowed : List α) : List α → Option α
  | [] => none
  | a :: tail => if a ∈ allowed then some a else front allowed tail

def Fits (D : Cases α) (rule : α → Option Bool) : Prop :=
  ∀ xs b, (xs,b) ∈ D → run rule xs = some b

def Possible (D : Cases α) (allowed : List α) : Prop :=
  ∃ rule, Fits D rule ∧ ∀ a, a ∉ allowed → rule a = none

def Wants [DecidableEq α] (D : Cases α) (allowed : List α) (a : α) (b : Bool) : Prop :=
  ∃ xs, (xs,b) ∈ D ∧ front allowed xs = some a

def Conflict [DecidableEq α] (D : Cases α) (allowed : List α) (a : α) : Prop :=
  Wants D allowed a false ∧ Wants D allowed a true

theorem front_mem [DecidableEq α] {A : List α} {a : α} :
    ∀ xs, front A xs = some a → a ∈ A := by
  intro xs
  induction xs with
  | nil => simp [front]
  | cons x xs ih =>
    by_cases h : x ∈ A
    · simpa [front, h] using fun e : x = a => e ▸ h
    · simpa [front, h] using ih

theorem skip_exhausted [DecidableEq α] {A : List α} {rule : α → Option Bool}
    (f : ∀ a, a ∉ A → rule a = none) :
    ∀ xs, front A xs = none → run rule xs = none := by
  intro xs
  induction xs with
  | nil => simp [run]
  | cons a xs ih =>
    by_cases h : a ∈ A
    · simp [front, h]
    · simpa [front, h, run, f a h] using ih

theorem stop_at_front [DecidableEq α] {A : List α} {rule : α → Option Bool}
    (f : ∀ a, a ∉ A → rule a = none) {a : α} {b : Bool}
    (label : rule a = some b) :
    ∀ xs, front A xs = some a → run rule xs = some b := by
  intro xs
  induction xs with
  | nil => simp [front]
  | cons x xs ih =>
    by_cases h : x ∈ A
    · intro e
      have eq : x = a := by simpa [front, h] using e
      subst x
      simp [run, label]
    · simpa [front, h, run, f x h] using ih

theorem conflict_forces_continue [DecidableEq α] {D : Cases α} {A : List α} {a : α}
    (both : Conflict D A a) {rule : α → Option Bool}
    (fits : Fits D rule) (outside : ∀ x, x ∉ A → rule x = none) : rule a = none := by
  obtain ⟨⟨xs, hxs, fx⟩, ⟨ys, hys, fy⟩⟩ := both
  cases h : rule a with
  | none => rfl
  | some b =>
    cases b with
    | false =>
      have v := stop_at_front outside h ys fy
      rw [fits ys true hys] at v
      contradiction
    | true =>
      have v := stop_at_front outside h xs fx
      rw [fits xs false hxs] at v
      contradiction

theorem erase_conflict [DecidableEq α] {D : Cases α} {A : List α} {a : α}
    (both : Conflict D A a) : Possible D A ↔ Possible D (A.erase a) := by
  constructor
  · rintro ⟨rule, fits, outside⟩
    refine ⟨rule, fits, ?_⟩
    intro x missing
    by_cases same : a = x
    · subst x
      exact conflict_forces_continue both fits outside
    · apply outside x
      intro mem
      exact missing ((List.mem_erase_of_ne (Ne.symm same)).mpr mem)
  · rintro ⟨rule, fits, outside⟩
    exact ⟨rule, fits, fun x h => outside x (fun h' => h (List.mem_of_mem_erase h'))⟩

theorem consistent_fronts [DecidableEq α] {D : Cases α} {A : List α}
    (live : ∀ xs b, (xs,b) ∈ D → front A xs ≠ none)
    (consistent : ∀ a, ¬ Conflict D A a) : Possible D A := by
  classical
  let rule (a : α) : Option Bool := if a ∈ A then some (decide (Wants D A a true)) else none
  have outside (a : α) (h : a ∉ A) : rule a = none := by simp [rule, h]
  refine ⟨rule, ?_, outside⟩
  intro xs b mem
  cases h : front A xs with
  | none => exact False.elim (live xs b mem h)
  | some a =>
    have inA := front_mem xs h
    have label : rule a = some b := by
      cases b with
      | true => have want : Wants D A a true := ⟨xs, mem, h⟩; simp [rule, inA, want]
      | false =>
        have noWant : ¬ Wants D A a true := fun v => consistent a ⟨⟨xs,mem,h⟩,v⟩
        simp [rule, inA, noWant]
    exact stop_at_front outside label xs h

/-- Any choice of a conflicting observation is allowed at each removal. -/
inductive Result [DecidableEq α] (D : Cases α) : List α → Bool → Prop
  | exhausted {A xs b} : (xs,b) ∈ D → front A xs = none → Result D A false
  | consistent {A} : (∀ xs b, (xs,b) ∈ D → front A xs ≠ none) →
      (∀ a, ¬ Conflict D A a) → Result D A true
  | remove {A a answer} : Conflict D A a → Result D (A.erase a) answer → Result D A answer

theorem result_correct [DecidableEq α] {D : Cases α} {A} {answer}
    (re : Result D A answer) : Possible D A ↔ answer = true := by
  induction re with
  | exhausted mem blocked =>
    constructor
    · rintro ⟨rule, fits, outside⟩
      have h := skip_exhausted outside _ blocked
      rw [fits _ _ mem] at h
      contradiction
    · simp
  | consistent live yes => exact ⟨fun _ => rfl, fun _ => consistent_fronts live yes⟩
  | remove both _ ih => exact (erase_conflict both).trans ih

theorem result_exists [DecidableEq α] (D : Cases α) (A : List α) : ∃ b, Result D A b := by
  classical
  by_cases dead : ∃ xs b, (xs,b) ∈ D ∧ front A xs = none
  · obtain ⟨xs,b,mem,noneHere⟩ := dead
    exact ⟨false,.exhausted mem noneHere⟩
  · by_cases conflict : ∃ a, Conflict D A a
    · obtain ⟨a, both⟩ := conflict
      have mem : a ∈ A := by
        obtain ⟨xs, _, hx⟩ := both.1
        exact front_mem xs hx
      have smaller : (A.erase a).length < A.length := by
        rw [List.length_erase_of_mem mem]
        have positive : 0 < A.length := List.length_pos_of_mem mem
        omega
      obtain ⟨b, h⟩ := result_exists D (A.erase a)
      exact ⟨b,.remove both h⟩
    · exact ⟨true,.consistent (fun xs b hi hn => dead ⟨xs,b,hi,hn⟩)
            (fun a hc => conflict ⟨a,hc⟩)⟩
termination_by A.length

end ForcedStoppingRules
