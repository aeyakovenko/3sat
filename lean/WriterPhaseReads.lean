import Std

namespace WriterPhaseReads

/-- Earlier phases are ordered newest first. 'none' means no write at this address. -/
def latest (initial : α) : List (Bool × Option α) → α
  | [] => initial
  | (_,some v) :: _ => v
  | (_,none) :: tail => latest initial tail

/-- A claimed latest writer must have a real final value. -/
def fromMask (initial : α) : List (Bool × Option α) → Option α
  | [] => some initial
  | (true,v) :: _ => v
  | (false,_) :: tail => fromMask initial tail

/-- Each store checks its own membership in the alleged writer-phase mask. -/
def NoMissing : List (Bool × Option α) → Prop
  | [] => True
  | (b,v) :: tail => (v.isSome = true → b = true) ∧ NoMissing tail

theorem sound {history : List (Bool × Option α)} {initial value : α}
    (checked : NoMissing history) (reply : fromMask initial history = some value) :
    latest initial history = value := by
  induction history with
  | nil => exact Option.some.inj reply
  | cons first rest ih =>
    obtain ⟨b,v⟩ := first
    obtain ⟨present,tailChecked⟩ := checked
    cases b with
    | false =>
      cases v with
      | none => exact ih tailChecked reply
      | some y => have impossible : false = true := present rfl; contradiction
    | true =>
      cases v with
      | none => contradiction
      | some y => exact Option.some.inj reply

def trueMask (h : List (Option α)) := h.map (fun v => (v.isSome,v))

theorem complete (history : List (Option α)) (initial : α) :
    NoMissing (trueMask history) ∧ fromMask initial (trueMask history) =
      some (latest initial (trueMask history)) := by
  induction history with
  | nil => exact ⟨True.intro,rfl⟩
  | cons a h ih =>
    obtain ⟨checks,reply⟩ := ih
    cases a with
    | none => exact ⟨⟨fun x => x,checks⟩,reply⟩
    | some v => exact ⟨⟨fun _ => rfl,checks⟩,rfl⟩

/-- A positive flag with no real store remains a failed retrieval until replaced. -/
inductive View where
  | zero
  | positive (payload : Option Nat)
  deriving DecidableEq

inductive Announcement where
  | silent
  | clear
  | positive
  deriving DecidableEq

def View.read : View → Option Nat
  | .zero => some 0
  | .positive p => p

def next (current : View) (store : Option Nat) : Announcement → Option View
  | .clear => if store = some 0 then some .zero else none
  | .positive => if store = some 0 then none else some (.positive store)
  | .silent =>
    match store with
    | none => some current
    | some 0 => if current = .zero then some .zero else none
    | some (_+1) => none

def Consistent (view : View) (actual : Nat) : Prop :=
  ∀ x, view.read = some x → actual = x

/-- A false positive flag may remain unusable. Every permitted boundary transition
    nevertheless preserves soundness of every subsequent successful read. -/
theorem next_sound (view result : View) (old : Nat) (store : Option Nat)
    (declare : Announcement) (before : Consistent view old)
    (checks : next view store declare = some result) :
    Consistent result (store.getD old) := by
  cases declare <;> cases store with
  | none =>
    all_goals cases view <;> cases result <;>
      simp_all [next,Consistent,View.read]
  | some n =>
    all_goals cases n <;> cases view <;> cases result <;>
      simp_all [next,Consistent,View.read]

def honestView : Nat → View
  | 0 => .zero
  | n+1 => .positive (some (n+1))

def honestAnnouncement (old : Nat) : Option Nat → Announcement
  | none => .silent
  | some 0 => if old = 0 then .silent else .clear
  | some (_+1) => .positive

/-- The true history uses a clear only when a positive old word becomes zero. -/
theorem next_complete (old : Nat) (store : Option Nat) :
    next (honestView old) store (honestAnnouncement old store)
      = some (honestView (store.getD old)) := by
  cases store with
  | none => rfl
  | some n => cases n <;> cases old <;> rfl

private theorem sum_of_perm (p : List.Perm (l : List Nat) r) : l.sum = r.sum := by
  induction p with
  | nil => rfl
  | cons x h ih => simp only [List.sum_cons,ih]
  | swap x y t => simp only [List.sum_cons]; omega
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

private theorem sum_le (l : List V) (f g : V → Nat)
    (h : ∀ v ∈ l, f v ≤ g v) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x tail ih =>
    have a := h x List.mem_cons_self
    have b := ih fun v hv => h v (List.mem_cons_of_mem x hv)
    simp only [List.map_cons,List.sum_cons]
    omega

private theorem eq_each (l : List V) (f g : V → Nat)
    (h : ∀ v ∈ l, f v ≤ g v) (eq : (l.map f).sum = (l.map g).sum) :
    ∀ v ∈ l, f v = g v := by
  induction l with
  | nil => simp
  | cons x tail ih =>
    have a := h x List.mem_cons_self
    have ht : ∀ v ∈ tail, f v ≤ g v := fun v hv => h v (List.mem_cons_of_mem x hv)
    have b := sum_le tail f g ht
    simp only [List.map_cons,List.sum_cons] at eq
    intro v hv
    rcases List.mem_cons.mp hv with e | mem
    · subst v; omega
    · exact ih ht (by omega) v mem

/-- A no-hit pass says that every digit of the Bob position is at most
    the matching digit of the Alice position. On permutations it proves equality. -/
theorem position_eq_of_no_hit (symbols : List V) (posA posB : V → I)
    (perm : (symbols.map posB).Perm (symbols.map posA))
    (code : K → I → Nat)
    (separates : ∀ i j, (∀ h, code h i = code h j) → i = j)
    (noHit : ∀ v ∈ symbols, ∀ h, code h (posB v) ≤ code h (posA v)) :
    ∀ v ∈ symbols, posB v = posA v := by
  intro v hv
  apply separates
  intro h
  have sums := sum_of_perm (perm.map (code h))
  simp only [List.map_map,Function.comp_def] at sums
  exact eq_each symbols _ _ (fun y hy => noHit y hy h) sums v hv

end WriterPhaseReads
