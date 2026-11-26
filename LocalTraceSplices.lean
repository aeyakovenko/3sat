import Std

/-! Local CPU paths may be joined freely once their two boundary controllers
and clock positions have been fixed and writable-memory checks omitted.
This file starts at that product hypothesis. -/

namespace LocalTraceSplices

def Weak {I B : Type} (menu : I → B → Prop) (path : I → B) : Prop :=
  ∀ i, menu i (path i)

theorem nonempty_iff {I B : Type} (menu : I → B → Prop) :
    (∃ path, Weak menu path) ↔ ∀ i, ∃ b, menu i b := by
  constructor
  · rintro ⟨path, h⟩ i
    exact ⟨path i, h i⟩
  · intro h
    exact ⟨fun i => Classical.choose (h i), fun i => Classical.choose_spec (h i)⟩

/-- Auxiliary labels can have many realizations of the same visible block. -/
theorem unique_visible_iff {I B T : Type} (menu : I → B → Prop)
    (visible : I → B → T) (reference : I → T) :
    ((∃ path, Weak menu path) ∧
      ∀ path, Weak menu path → (fun i => visible i (path i)) = reference) ↔
    (∀ i, ∃ b, menu i b) ∧
      (∀ i b, menu i b → visible i b = reference i) := by
  classical
  constructor
  · rintro ⟨⟨base, hb⟩, uniq⟩
    refine ⟨fun i => ⟨base i, hb i⟩, ?_⟩
    intro i b valid
    let splice := fun j => if j = i then b else base j
    have good : Weak menu splice := by
      intro j
      by_cases eq : j = i
      · subst j
        simpa [splice] using valid
      · simpa [splice, eq] using hb j
    simpa [splice] using congrFun (uniq splice good) i
  · rintro ⟨nonempty, localUnique⟩
    exact ⟨(nonempty_iff _).2 nonempty, fun path hp =>
      funext (fun i => localUnique i (path i) (hp i))⟩

/-- The read, the proposed last writer and exclusion of intervening stores
can all be imposed by restrictions on individual time slots. Fixing the
certificate before choosing the blocks is essential. -/
theorem certificate_splice {I B Tag Time : Type} (menu : I → B → Prop)
    (owner : Time → I) (admissible : Tag → Prop)
    (atSlot : Tag → Time → B → Prop) :
    (∃ c path, admissible c ∧ Weak menu path ∧
       ∀ t, atSlot c t (path (owner t))) ↔
    (∃ c, admissible c ∧ ∀ i, ∃ b, menu i b ∧
       ∀ t, owner t = i → atSlot c t b) := by
  constructor
  · rintro ⟨c, path, hc, hp, checks⟩
    refine ⟨c, hc, fun i => ⟨path i, hp i, ?_⟩⟩
    intro t ht
    simpa [← ht] using checks t
  · rintro ⟨c, hc, blocks⟩
    let path := fun i => Classical.choose (blocks i)
    have props := fun i => Classical.choose_spec (blocks i)
    exact ⟨c, path, hc, fun i => (props i).1,
      fun t => (props (owner t)).2 t rfl⟩

/-- Each event is projected to a single watched address. Other addresses,
CPU steps, and empty slots have the same effect as a quiet event. -/
inductive Event (W : Type) where
  | quiet
  | store (v : W)
  | read (v : W)
  deriving DecidableEq

namespace Event

def applyTo {W : Type} (e : Event W) (w : W) : W :=
  match e with
  | .store v => v
  | _ => w

def agrees {W : Type} (e : Event W) (w : W) : Prop :=
  match e with
  | .read v => v = w
  | _ => True

def noWrite {W : Type} (e : Event W) : Prop :=
  match e with
  | .store _ => False
  | _ => True

end Event

def finalWord {W : Type} (initial : W) (xs : List (Event W)) : W :=
  xs.foldl (fun w e => e.applyTo w) initial

theorem finalWord_append {W : Type} (w : W) (xs ys : List (Event W)) :
    finalWord w (xs ++ ys) = finalWord (finalWord w xs) ys :=
  List.foldl_append

def consistent {W : Type} (w : W) : List (Event W) → Prop
  | [] => True
  | e :: es => e.agrees w ∧ consistent (e.applyTo w) es

/-- A memory fault is exactly a read with the wrong incoming value. -/
theorem inconsistent_iff {W : Type} (w : W) (xs : List (Event W)) :
    ¬consistent w xs ↔ ∃ before v after,
      xs = before ++ Event.read v :: after ∧ v ≠ finalWord w before := by
  induction xs generalizing w with
  | nil => simp [consistent]
  | cons e xs ih =>
    constructor
    · intro bad
      by_cases he : e.agrees w
      · have later : ¬consistent (e.applyTo w) xs := fun h => bad ⟨he, h⟩
        obtain ⟨before, v, after, eq, wrong⟩ := (ih _).1 later
        exact ⟨e :: before, v, after, by simp [eq], wrong⟩
      · cases e with
        | quiet => exact False.elim (he trivial)
        | store v => exact False.elim (he trivial)
        | read v => exact ⟨[], v, xs, rfl, he⟩
    · rintro ⟨before, v, after, eq, wrong⟩ ⟨first, rest⟩
      cases before with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at eq
        obtain ⟨rfl, _⟩ := eq
        exact wrong first
      | cons e' before =>
        simp only [List.cons_append, List.cons.injEq] at eq
        obtain ⟨rfl, eq⟩ := eq
        exact (ih _).2 ⟨before, v, after, eq, wrong⟩ rest

/-- The incoming value is either the initial value with no previous store,
or the value at a designated store with a store-free suffix. -/
theorem latest_source {W : Type} (w : W) (xs : List (Event W)) :
    ((∀ e ∈ xs, e.noWrite) ∧ finalWord w xs = w) ∨
      ∃ before v gap, xs = before ++ Event.store v :: gap ∧
        (∀ e ∈ gap, e.noWrite) ∧ finalWord w xs = v := by
  induction xs generalizing w with
  | nil => exact Or.inl ⟨by simp, rfl⟩
  | cons e xs ih =>
    rcases ih (e.applyTo w) with ⟨clean, same⟩ | ⟨before, v, gap, eq, clean, same⟩
    · cases e with
      | quiet => exact Or.inl ⟨by simpa [Event.noWrite] using clean, same⟩
      | read v => exact Or.inl ⟨by simpa [Event.noWrite] using clean, same⟩
      | store v => exact Or.inr ⟨[], v, xs, rfl, clean, same⟩
    · exact Or.inr ⟨e :: before, v, gap, by simp [eq], clean, same⟩

theorem store_free_value {W : Type} (w : W) (xs : List (Event W))
    (clean : ∀ e ∈ xs, e.noWrite) : finalWord w xs = w := by
  rcases latest_source w xs with ⟨_, same⟩ | ⟨before, v, gap, eq, _, _⟩
  · exact same
  · have mem : Event.store v ∈ xs := by simp [eq]
    exact False.elim (clean _ mem)

/-- This source description only mentions events and a store-free interval. -/
def Source {W : Type} (initial : W) (xs : List (Event W)) (value : W) : Prop :=
  ((∀ e ∈ xs, e.noWrite) ∧ value = initial) ∨
    ∃ before gap, xs = before ++ Event.store value :: gap ∧ ∀ e ∈ gap, e.noWrite

theorem source_iff {W : Type} (initial : W) (xs : List (Event W)) (value : W) :
    Source initial xs value ↔ finalWord initial xs = value := by
  constructor
  · rintro (⟨clean, rfl⟩ | ⟨before, gap, eq, clean⟩)
    · exact store_free_value _ xs clean
    · rw [eq, finalWord_append]
      exact store_free_value value gap clean
  · intro same
    rcases latest_source initial xs with ⟨clean, eq⟩ | ⟨before, v, gap, eq, clean, last⟩
    · exact Or.inl ⟨clean, same.symm.trans eq⟩
    · have hv : v = value := last.symm.trans same
      exact Or.inr ⟨before, gap, by simpa [hv] using eq, clean⟩

theorem inconsistent_iff_source {W : Type} (initial : W) (xs : List (Event W)) :
    ¬consistent initial xs ↔ ∃ before reply after value,
      xs = before ++ Event.read reply :: after ∧
      Source initial before value ∧ reply ≠ value := by
  rw [inconsistent_iff]
  constructor
  · rintro ⟨before, reply, after, eq, wrong⟩
    exact ⟨before, reply, after, finalWord initial before, eq,
      (source_iff _ _ _).2 rfl, wrong⟩
  · rintro ⟨before, reply, after, value, eq, source, wrong⟩
    exact ⟨before, reply, after, eq, fun same =>
      wrong (same.trans ((source_iff _ _ _).1 source))⟩

end LocalTraceSplices
