import Std

namespace AdviceTableExhaustion

/-- A row records one reply at each of d possible suffixes. -/
def Table : Nat → Type
  | 0 => Unit
  | d+1 => Bool × Table d

private def tails {α : Type} (b : Bool) : List (Bool × α) → List α
  | [] => []
  | (c,x) :: rest => if c = b then x :: tails b rest else tails b rest

private theorem tails_length {α : Type} (rows : List (Bool × α)) :
    (tails false rows).length + (tails true rows).length = rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨b,x⟩
    cases b <;> simp [tails] <;> omega

private theorem tail_represented {α : Type} (b : Bool) (x : α) (rows : List (Bool × α))
    (present : (b,x) ∈ rows) : x ∈ tails b rows := by
  induction rows with
  | nil => contradiction
  | cons row rest ih =>
    rcases row with ⟨c,y⟩
    rcases List.mem_cons.mp present with h | h
    · cases h
      simp [tails]
    · have inside := ih h
      by_cases eq : c = b <;> simp [tails, eq, inside]

/-- Recursively choose a deficient half of the list. Repeated predicted rows
    are allowed. For d=0 even the empty truth table counts as a table. -/
theorem missing (d : Nat) (rows : List (Table d)) (short : rows.length < 2^d) :
    ∃ t : Table d, t ∉ rows := by
  induction d with
  | zero =>
    cases rows with
    | nil => exact ⟨(), by simp⟩
    | cons row rest => simp at short
  | succ d ih =>
    have sum := tails_length rows
    rw [Nat.pow_succ] at short
    by_cases first : (tails false rows).length < 2^d
    · obtain ⟨t,hm⟩ := ih (tails false rows) first
      exact ⟨(false,t), fun h => hm (tail_represented false t rows h)⟩
    · obtain ⟨t,hm⟩ := ih (tails true rows) (by omega)
      exact ⟨(true,t), fun h => hm (tail_represented true t rows h)⟩

def read : (d : Nat) → Table d → Fin d → Bool
  | 0, _, i => Fin.elim0 i
  | d+1, (b,t), i => Fin.cases b (read d t) i

def pack : (d : Nat) → (Fin d → Bool) → Table d
  | 0, _ => ()
  | d+1, f => (f 0, pack d (fun i => f i.succ))

private theorem read_pack (d : Nat) (f : Fin d → Bool) (i : Fin d) :
    read d (pack d f) i = f i := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih (fun j => f j.succ) j

private theorem row_ext (d : Nat) (t u : Table d)
    (agree : ∀ i, read d t i = read d u i) : t = u := by
  induction d with
  | zero => cases t; cases u; rfl
  | succ d ih =>
    rcases t with ⟨b,t⟩
    rcases u with ⟨c,u⟩
    have heads : b = c := agree 0
    have rest := ih t u (fun j => agree j.succ)
    cases heads
    cases rest
    rfl

/-- One truth table disagrees somewhere with the row of each of the 2^s
    advice values. All rows may depend on the same fixed source prefix. -/
theorem advice_gap (d s : Nat) (short : s < d)
    (predict : Nat → Fin d → Bool) :
    ∃ truth : Fin d → Bool, ∀ a < 2^s, ∃ i, predict a i ≠ truth i := by
  classical
  let rows := (List.range (2^s)).map (fun a => pack d (predict a))
  have count : rows.length < 2^d := by
    simpa [rows] using Nat.pow_lt_pow_of_lt (a:=2) (by decide) short
  obtain ⟨t, absent⟩ := missing d rows count
  refine ⟨read d t, ?_⟩
  intro a ha
  apply Classical.byContradiction
  intro every
  have agree (i : Fin d) : predict a i = read d t i := by
    by_cases h : predict a i = read d t i
    · exact h
    · exact False.elim (every ⟨i,h⟩)
  have same : t = pack d (predict a) :=
    row_ext d t _ (fun i => (agree i).symm.trans (read_pack d (predict a) i).symm)
  apply absent
  rw [same]
  exact List.mem_map_of_mem (List.mem_range.mpr ha)

/-- A completed capped row can use different defaults on every timeout.
    If its fast replies are correct for the selected table, some timeout
    conceals a disagreement between the default and the actual target bit. -/
theorem capped_gap (d s : Nat) (short : s < d)
    (capped : Nat → Fin d → Option Bool) (fallback : Nat → Fin d → Bool) :
    ∃ truth : Fin d → Bool, ∀ a < 2^s,
      (∀ i v, capped a i = some v → v = truth i) →
      ∃ i, capped a i = none ∧ fallback a i ≠ truth i := by
  obtain ⟨truth, gap⟩ := advice_gap d s short
    (fun a i => (capped a i).getD (fallback a i))
  refine ⟨truth, ?_⟩
  intro a ha correct
  obtain ⟨i, diff⟩ := gap a ha
  cases hc : capped a i with
  | none => exact ⟨i, hc, by simpa [hc] using diff⟩
  | some v => exact False.elim (diff (by simpa [hc] using correct i v hc))

/-- Specialization to every binary suffix of length r (coded in [0,2^r)).
    Agreement of a joined program on the true table together with faithful
    capped execution supplies the fast-reply hypothesis above. -/
theorem joined_timeout (r s : Nat) (short : s < 2^r)
    (capped : Nat → Fin (2^r) → Option Bool) (fallback joined : Nat → Fin (2^r) → Bool)
    (faithful : ∀ a i v, capped a i = some v → v = joined a i) :
    ∃ truth : Fin (2^r) → Bool, ∀ a < 2^s,
      (∀ i, joined a i = truth i) →
      ∃ i, capped a i = none ∧ fallback a i ≠ joined a i := by
  obtain ⟨truth, fail⟩ := capped_gap (2^r) s short capped fallback
  refine ⟨truth, ?_⟩
  intro a ha exactRow
  obtain ⟨i, timeout, diff⟩ := fail a ha (fun i v hv => (faithful a i v hv).trans (exactRow i))
  exact ⟨i, timeout, (exactRow i).symm ▸ diff⟩

end AdviceTableExhaustion
