import Std

/-! Replay of finite tape or RAM segments that access one writable block each.
The source runs share a controller schedule, addressed block schedule, and
initial memory. Their input observations and modified block values may differ.
Each local transition can describe a nondeterministic segment of any duration. -/

namespace BlockEpochSplice

variable {Addr Word Source View Control : Type} [DecidableEq Addr]

def write (m : Addr → Word) (a : Addr) (v : Word) : Addr → Word :=
  fun x => if x = a then v else m x

/-- Entire memory after the first t recorded writes, including all untouched blocks. -/
def memory (init : Addr → Word) (block : Nat → Addr) (out : Nat → Word) :
    Nat → Addr → Word
  | 0 => init
  | t + 1 => write (memory init block out t) (block t) (out t)

/-- The most recent visit to this block strictly before t. -/
def previous (block : Nat → Addr) : Nat → Addr → Option Nat
  | 0, _ => none
  | t + 1, a => if a = block t then some t else previous block t a

theorem previous_before (block : Nat → Addr) (t : Nat) (a : Addr) (r : Nat)
    (h : previous block t a = some r) : r < t := by
  induction t with
  | zero => simp [previous] at h
  | succ t ih =>
    by_cases same : a = block t
    · simp [previous, same] at h
      omega
    · have old : previous block t a = some r := by simpa [previous, same] using h
      exact Nat.lt_trans (ih old) (Nat.lt_succ_self t)

theorem memory_from_previous (init : Addr → Word) (block : Nat → Addr)
    (out : Nat → Word) (t : Nat) (a : Addr) :
    memory init block out t a = (previous block t a).elim (init a) out := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases written : a = block t <;> simp [memory, write, previous, written, ih]

/-- A path with the specified boundary controllers (in particular the final one).
The local relation receives just the visible input and the entering writable block.
The full memory update preserves every other block. -/
def Runs (n : Nat) (step : Nat → View → Control → Word → Control → Word → Prop)
    (observe : Nat → View) (ctrl : Nat → Control) (block : Nat → Addr)
    (init : Addr → Word) : Prop :=
  ∃ states : Nat → Addr → Word, states 0 = init ∧
    ∀ t < n, ∃ value,
      step t (observe t) (ctrl t) (states t (block t)) (ctrl (t+1)) value ∧
      states (t+1) = write (states t) (block t) value

/-- If the previous writer is chosen from the other source, either source must
supply the same outgoing value for that particular previous write. -/
def Compatible (n : Nat) (block : Nat → Addr) (out : Source → Nat → Word)
    (pick : Nat → Source) : Prop :=
  ∀ t < n, ∀ r, previous block t (block t) = some r →
    pick r ≠ pick t → out (pick r) r = out (pick t) r

theorem replay (n : Nat) (step : Nat → View → Control → Word → Control → Word → Prop)
    (view : Source → Nat → View) (mixed : Nat → View) (ctrl : Nat → Control)
    (block : Nat → Addr) (init : Addr → Word) (out : Source → Nat → Word)
    (pick : Nat → Source)
    (legal : ∀ s t, t < n → step t (view s t) (ctrl t)
      (memory init block (out s) t (block t)) (ctrl (t+1)) (out s t))
    (reads : ∀ t < n, mixed t = view (pick t) t)
    (edges : Compatible n block out pick) : Runs n step mixed ctrl block init := by
  let selected := fun r => out (pick r) r
  refine ⟨memory init block selected, rfl, ?_⟩
  intro t ht
  refine ⟨out (pick t) t, ?_, rfl⟩
  have entry : memory init block selected t (block t) =
      memory init block (out (pick t)) t (block t) := by
    rw [memory_from_previous, memory_from_previous]
    cases h : previous block t (block t) with
    | none => rfl
    | some r =>
      change out (pick r) r = out (pick t) r
      by_cases same : pick r = pick t
      · rw [same]
      · exact edges t ht r h same
  rw [entry, reads t ht]
  exact legal (pick t) t ht

/-- At a separator, both incoming and outgoing block contents are recorded.
Every previous-visit edge that changes source has at least one endpoint there.
Together these statements imply precisely the edge agreements required by replay. -/
theorem compatible_of_cut (n : Nat) (block : Nat → Addr) (init : Addr → Word)
    (out : Source → Nat → Word) (pick : Nat → Source) (cut : Nat → Prop)
    (separates : ∀ t < n, ∀ r, previous block t (block t) = some r →
        pick r ≠ pick t → cut r ∨ cut t)
    (exit_agree : ∀ r < n, cut r → ∀ s u, out s r = out u r)
    (entry_agree : ∀ t < n, cut t → ∀ s u,
        memory init block (out s) t (block t) = memory init block (out u) t (block t)) :
    Compatible n block out pick := by
  intro t ht r prev different
  rcases separates t ht r prev different with hr | hcut
  · exact exit_agree r (Nat.lt_trans (previous_before block t (block t) r prev) ht) hr (pick r) (pick t)
  · have eq := entry_agree t ht hcut (pick r) (pick t)
    simpa only [memory_from_previous, prev, Option.elim] using eq

end BlockEpochSplice

namespace BlockEpochSplice.LevelCode

/-- The first level is at most the public ceiling and each later level is at
most its predecessor. Zero is an ordinary level, available as a sentinel. -/
def Bounded : Nat → List Nat → Prop
  | _, [] => True
  | b, x :: xs => x ≤ b ∧ Bounded x xs

/-- False decreases the level by one; true emits the current level. -/
def encode : Nat → List Nat → List Bool
  | _, [] => []
  | b, x :: xs => List.replicate (b - x) false ++ true :: encode x xs

def decode : Nat → List Bool → List Nat
  | _, [] => []
  | b, false :: bits => decode (b-1) bits
  | b, true :: bits => b :: decode b bits

private theorem decode_drops (d b : Nat) (tail : List Bool) :
    decode b (List.replicate d false ++ tail) = decode (b - d) tail := by
  induction d generalizing b with
  | zero => simp
  | succ d ih =>
    simp only [List.replicate_succ, List.cons_append, decode, ih]
    congr 1
    omega

theorem roundtrip {b : Nat} {xs : List Nat} (h : Bounded b xs) :
    decode b (encode b xs) = xs := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨le, ht⟩ := h
    simp only [encode, decode_drops]
    have restored : b - (b-x) = x := by omega
    simp [restored, decode, ih ht]

theorem encoded_length {b : Nat} {xs : List Nat} (h : Bounded b xs) :
    (encode b xs).length ≤ xs.length + b := by
  induction xs generalizing b with
  | nil => simp [encode]
  | cons x xs ih =>
    obtain ⟨le, ht⟩ := h
    have tailBound := ih ht
    simp only [encode, List.length_append, List.length_replicate, List.length_cons]
    omega

theorem encode_injective {b : Nat} {xs ys : List Nat}
    (hx : Bounded b xs) (hy : Bounded b ys) (e : encode b xs = encode b ys) :
    xs = ys := by
  simpa only [roundtrip hx, roundtrip hy] using congrArg (decode b) e

/-- Parse a fixed number of emitted levels and return the rest of the stream. -/
def read : List Bool → Nat → Nat → Option (List Nat × List Bool)
  | bits, 0, _ => some ([], bits)
  | [], _ + 1, _ => none
  | false :: bits, q + 1, b => read bits (q + 1) (b - 1)
  | true :: bits, q + 1, b => do
    let (xs, rest) ← read bits q b
    return (b :: xs, rest)

private theorem read_drops (d b q : Nat) (tail : List Bool) :
    read (List.replicate d false ++ tail) (q+1) b = read tail (q+1) (b-d) := by
  induction d generalizing b with
  | zero => simp
  | succ d ih =>
    simp only [List.replicate_succ, List.cons_append, read, ih]
    congr 1
    omega

theorem read_with_suffix {b : Nat} {xs : List Nat} (h : Bounded b xs)
    (suffix : List Bool) :
    read (encode b xs ++ suffix) xs.length b = some (xs, suffix) := by
  induction xs generalizing b with
  | nil => simp [encode, read]
  | cons x xs ih =>
    obtain ⟨le, ht⟩ := h
    have restored : b - (b-x) = x := by omega
    simp [encode, List.append_assoc, read_drops, restored, read, ih ht]

/-- Use zero for no changes and one plus the exponent for a positive count. -/
def level (x : Nat) : Nat := if x = 0 then 0 else x.log2 + 1

def lowerCount : Nat → Nat
  | 0 => 0
  | j+1 => 2^j

theorem level_monotone {x y : Nat} (xy : x ≤ y) : level x ≤ level y := by
  by_cases hx : x = 0
  · simp [level, hx]
  · have hy : y ≠ 0 := by omega
    have logs : x.log2 ≤ y.log2 := (Nat.le_log2 hy).2 (Nat.le_trans (Nat.log2_self_le hx) xy)
    simp [level, hx, hy, logs]

/-- Clipping and converting counts to levels preserves their order. The
public starting ceiling depends only on cap, even for unbounded raw counts. -/
theorem clipped_levels {b : Nat} {xs : List Nat} (h : Bounded b xs) (cap : Nat) :
    Bounded (level (min cap b)) (xs.map (fun x => level (min cap x))) := by
  induction xs generalizing b with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨le, ht⟩ := h
    exact ⟨level_monotone (by omega), ih ht⟩

theorem clipped_length {b : Nat} {xs : List Nat} (h : Bounded b xs) (cap : Nat) :
    (encode (level cap) (xs.map (fun x => level (min cap x)))).length
      ≤ xs.length + level cap := by
  have valid : Bounded (level cap) (xs.map (fun x => level (min cap x))) := by
    cases xs with
    | nil => trivial
    | cons x xs => exact ⟨level_monotone (Nat.min_le_left _ _), clipped_levels h.2 cap⟩
  simpa using encoded_length valid

theorem lowerCount_bounds (x : Nat) :
    lowerCount (level x) ≤ x ∧ x ≤ 2 * lowerCount (level x) := by
  by_cases hx : x = 0
  · simp [hx, level, lowerCount]
  · have h := Nat.lt_log2_self (n := x)
    rw [Nat.pow_succ] at h
    simp only [level, if_neg hx, lowerCount]
    exact ⟨Nat.log2_self_le hx, by omega⟩

def rounded (cap x : Nat) : Nat := lowerCount (level (min cap x))

/-- A summed threshold reached before the cut and no greater than the cap
retains at least half its value, even if one segment already exceeds the cap. -/
theorem summed_threshold (cap : Nat) (xs : List Nat) {threshold : Nat}
    (underCap : threshold ≤ cap) (reached : threshold ≤ xs.sum) :
    threshold ≤ 2 * (xs.map (rounded cap)).sum := by
  suffices h : min cap xs.sum ≤ 2 * (xs.map (rounded cap)).sum by omega
  clear underCap reached threshold
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have first := (lowerCount_bounds (min cap x)).2
    change min cap x ≤ 2 * rounded cap x at first
    simp only [List.sum_cons, List.map_cons]
    omega

end BlockEpochSplice.LevelCode
