import Std

/-! Exact equality of aligned, deterministic native records. Reads record their
replies. A blind store records its address and payload without reading the old
value. A multi-access instruction can be represented by controller substeps. -/
namespace FirstReadBeforeOverwrite

universe u v w
variable {A : Type u} {V : Type v} {C : Type w}

inductive Op (A : Type u) (V : Type v) where
  | idle
  | load (addr : A)
  | store (addr : A) (value : V)

abbrev Mem (A : Type u) (V : Type v) := A → V

def reply (m : Mem A V) : Op A V → Option V
  | .load a => some (m a)
  | _ => none

def update [DecidableEq A] (m : Mem A V) : Op A V → Mem A V
  | .store a v => fun i => if i = a then v else m i
  | _ => m

structure Program (A : Type u) (V : Type v) (C : Type w) where
  issue : C → Op A V
  advance : C → Option V → C

structure Record (A : Type u) (V : Type v) (C : Type w) where
  before : C
  op : Op A V
  answer : Option V
  after : C

def record (p : Program A V C) (c : C) (m : Mem A V) : Record A V C :=
  let op := p.issue c
  let r := reply m op
  ⟨c, op, r, p.advance c r⟩

def trace [DecidableEq A] (p : Program A V C) :
    Nat → C → Mem A V → List (Record A V C)
  | 0, _, _ => []
  | n+1, c, m =>
    let head := record p c m
    head :: trace p n head.after (update m head.op)

/-- True exactly when a read of this address precedes every store to it in
the segment, including the case where the segment has no such store. -/
def incoming (a : A) : List (Record A V C) → Prop
  | [] => False
  | r :: rs => match r.op with
    | .idle => incoming a rs
    | .load i => a = i ∨ incoming a rs
    | .store i _ => a ≠ i ∧ incoming a rs

def agrees (m m' : Mem A V) (rs : List (Record A V C)) : Prop :=
  ∀ a, incoming a rs → m a = m' a

theorem agrees_cons [DecidableEq A] (m m' : Mem A V) (r : Record A V C)
    (rs : List (Record A V C)) :
    agrees m m' (r :: rs) ↔
    reply m r.op = reply m' r.op ∧ agrees (update m r.op) (update m' r.op) rs := by
  cases h : r.op with
  | idle => simp [agrees, incoming, h, reply, update]
  | load i =>
    simp only [agrees, incoming, h, reply, update, Option.some.injEq]
    exact ⟨fun all => ⟨all i (Or.inl rfl), fun a ha => all a (Or.inr ha)⟩,
      fun ⟨eq, rest⟩ a ha => ha.elim (fun e => e ▸ eq) (rest a)⟩
  | store i v =>
    simp only [agrees, incoming, h, reply, update, true_and]
    constructor
    · intro all a ha
      by_cases e : a = i
      · simp [e]
      · simpa [e] using all a ⟨e, ha⟩
    · intro all a ha
      simpa [ha.1] using all a ha.2

theorem trace_eq_iff [DecidableEq A] (p : Program A V C) (n : Nat)
    (c : C) (m m' : Mem A V) :
    trace p n c m = trace p n c m' ↔ agrees m m' (trace p n c m) := by
  induction n generalizing c m m' with
  | zero => simp [trace, agrees, incoming]
  | succ n ih =>
    simp only [trace, List.cons.injEq, agrees_cons]
    change (record p c m = record p c m' ∧
      trace p n (p.advance c (reply m (p.issue c))) (update m (p.issue c)) =
      trace p n (p.advance c (reply m' (p.issue c))) (update m' (p.issue c))) ↔
      reply m (p.issue c) = reply m' (p.issue c) ∧
      agrees (update m (p.issue c)) (update m' (p.issue c))
        (trace p n (p.advance c (reply m (p.issue c))) (update m (p.issue c)))
    by_cases eq : reply m (p.issue c) = reply m' (p.issue c)
    · have hrec : record p c m = record p c m' := by simp [record, eq]
      simp only [eq, hrec, true_and, ih]
    · have hrec : record p c m ≠ record p c m' :=
        fun h => eq (congrArg Record.answer h)
      simp [eq, hrec]

def writesHere (a : A) (r : Record A V C) : Prop :=
  match r.op with | .store i _ => a = i | _ => False

def written (a : A) : List (Record A V C) → Prop
  | [] => False
  | r :: rs => writesHere a r ∨ written a rs

/-- The recursive test is equivalent to a particular load with no
same-address store anywhere in its preceding list prefix. -/
theorem incoming_split_iff (a : A) (rs : List (Record A V C)) :
    incoming a rs ↔ ∃ pre r post, rs = pre ++ r :: post ∧
      r.op = .load a ∧ ¬written a pre := by
  constructor
  · induction rs with
    | nil => simp [incoming]
    | cons r rs ih =>
      intro hi
      have later (hw : ¬writesHere a r) (tailRead : incoming a rs) :
          ∃ pre r' post, r :: rs = pre ++ r' :: post ∧ r'.op = .load a ∧ ¬written a pre := by
        obtain ⟨pre, r', post, eq, hr', ns⟩ := ih tailRead
        exact ⟨r :: pre, r', post, congrArg (r :: ·) eq, hr',
          fun h => h.elim hw ns⟩
      cases op : r.op with
      | idle => exact later (by simp [writesHere, op]) (by simpa [incoming, op] using hi)
      | load i =>
        cases (show a = i ∨ incoming a rs by simpa [incoming, op] using hi) with
        | inl eq =>
          subst i
          exact ⟨[], r, rs, rfl, op, by simp [written]⟩
        | inr ht => exact later (by simp [writesHere, op]) ht
      | store i v =>
        obtain ⟨hn, ht⟩ := (show a ≠ i ∧ incoming a rs by simpa [incoming, op] using hi)
        exact later (by simpa [writesHere, op] using hn) ht
  · rintro ⟨pre, r, post, rfl, hr, hw⟩
    induction pre with
    | nil => simp [incoming, hr]
    | cons head pre ih =>
      have ht := ih (fun h => hw (Or.inr h))
      have hn : ¬writesHere a head := fun h => hw (Or.inl h)
      cases op : head.op <;> simp_all [incoming, writesHere]

/-- The final memory is obtained by applying the recorded blind stores. -/
def finalMemory [DecidableEq A] (m : Mem A V) : List (Record A V C) → Mem A V
  | [] => m
  | r :: rs => finalMemory (update m r.op) rs

theorem final_diff [DecidableEq A] (rs : List (Record A V C)) (m m' : Mem A V) (a : A) :
    finalMemory m rs a ≠ finalMemory m' rs a ↔ m a ≠ m' a ∧ ¬ written a rs := by
  induction rs generalizing m m' with
  | nil => simp [finalMemory, written]
  | cons r rs ih =>
    simp only [finalMemory, written, ih]
    cases h : r.op with
    | idle => simp [update, writesHere, h]
    | load i => simp [update, writesHere, h]
    | store i v =>
      by_cases same : a = i <;> simp [update, writesHere, h, same]

theorem aligned_final_diff [DecidableEq A] (p : Program A V C) (n : Nat)
    (c : C) (m m' : Mem A V) (a : A) (h : agrees m m' (trace p n c m)) :
    finalMemory m (trace p n c m) a ≠ finalMemory m' (trace p n c m') a ↔
    m a ≠ m' a ∧ ¬written a (trace p n c m) := by
  rw [← (trace_eq_iff p n c m m').mpr h]
  exact final_diff _ _ _ _

end FirstReadBeforeOverwrite
