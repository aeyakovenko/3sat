import Std

namespace LiteralBranchParity

abbrev Bits := List Bool

/-- Big-endian encoding of a positive name index, with a one at the sentinel. -/
def marked (padding : Nat) (bits : Bits) : Bits :=
  List.replicate padding false ++ true :: bits

/-- The index 2^|name| + bin(name) represented in D+1 positions for |name| ≤ D. -/
def frame (D : Nat) (name : Bits) : Bits := marked (D - name.length) name

def bin : Bits → Nat
  | [] => 0
  | b :: bs => (if b then 2 ^ bs.length else 0) + bin bs

private theorem marked_value (a : Nat) (name : Bits) :
    bin (marked a name) = 2 ^ name.length + bin name := by
  induction a with
  | zero => simp [marked, bin]
  | succ a ih =>
    change bin (false :: marked a name) = _
    simpa [bin] using ih

theorem frame_value (D : Nat) (name : Bits) :
    bin (frame D name) = 2 ^ name.length + bin name :=
  marked_value _ _

/-- Conjunction of positive and negative bit literals in the prefix.
    On the Boolean cube these are the factors x and 1+x over F₂. -/
def literalProduct : Bits → Bits → Bool
  | [], _ => true
  | _ :: _, [] => false
  | true :: tail, x :: xs => x && literalProduct tail xs
  | false :: tail, x :: xs => !x && literalProduct tail xs

theorem literalProduct_spec (pattern bits : Bits) :
    literalProduct pattern bits = true ↔ List.IsPrefix pattern bits := by
  induction pattern generalizing bits with
  | nil => simp [literalProduct]
  | cons b bs ih =>
    cases bits with
    | nil => cases b <;> simp [literalProduct]
    | cons x xs => cases b <;> cases x <;> simp [literalProduct, ih]

theorem frame_width {D : Nat} {name : Bits} (fits : name.length ≤ D) :
    (frame D name).length = D + 1 := by
  simp [frame, marked]
  omega

private theorem marked_prefix (a b : Nat) (h x : Bits) :
    List.IsPrefix (marked a h) (marked b x) ↔ a = b ∧ List.IsPrefix h x := by
  induction a generalizing b with
  | zero => cases b <;> simp [marked, List.replicate_succ]
  | succ a ih =>
    cases b with
    | zero => simp [marked, List.replicate_succ]
    | succ b =>
      change List.IsPrefix (false :: marked a h) (false :: marked b x) ↔ _
      simp [ih]

/-- A literal prefix on the index bits simultaneously enforces the branch
    header and the exact payload length. The empty header and ordinal are allowed. -/
theorem selects_exactly_branch {D k : Nat} (header name : Bits)
    (branchFits : header.length + k ≤ D) (nameFits : name.length ≤ D) :
    List.IsPrefix (marked (D - (header.length + k)) header) (frame D name) ↔
      ∃ ordinal : Bits, ordinal.length = k ∧ name = header ++ ordinal := by
  rw [frame, marked_prefix]
  constructor
  · rintro ⟨samePadding, ordinal, he⟩
    have lengths := congrArg List.length he
    simp only [List.length_append] at lengths
    exact ⟨ordinal, by omega, he.symm⟩
  · rintro ⟨ordinal, width, rfl⟩
    exact ⟨by simp [width], List.prefix_append _ _⟩

/-- All literal names through a maximum length, each listed once. -/
def names : Nat → List Bits
  | 0 => [[]]
  | D+1 => [] :: ((names D).map (false :: ·) ++ (names D).map (true :: ·))

theorem mem_names (D : Nat) (p : Bits) : p ∈ names D ↔ p.length ≤ D := by
  induction D generalizing p with
  | zero => cases p <;> simp [names]
  | succ D ih =>
    cases p with
    | nil => simp [names]
    | cons b bs => cases b <;> simp [names, ih]

theorem names_distinct (D : Nat) : (names D).Nodup := by
  induction D with
  | zero => simp [names]
  | succ D ih =>
    apply List.nodup_cons.2
    constructor
    · simp
    · apply List.pairwise_append.2
      refine ⟨?_, ?_, ?_⟩
      · exact List.pairwise_map.2 (ih.imp (fun h he => h (List.cons.inj he).2))
      · exact List.pairwise_map.2 (ih.imp (fun h he => h (List.cons.inj he).2))
      · intro a ha b hb
        obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha
        obtain ⟨_, _, rfl⟩ := List.mem_map.1 hb
        simp

/-- The interpreter restricted to the desired printing and timing event.
    Using none permits arbitrary non-halting, late or otherwise invalid names. -/
def fiber {α : Type} [DecidableEq α] (D k : Nat) (header : Bits)
    (run : Bits → Option α) (y : α) : List Bits :=
  (names D).filter fun p =>
    (marked (D - (header.length + k)) header).isPrefixOf (frame D p) &&
      decide (run p = some y)

theorem mem_fiber {α : Type} [DecidableEq α] {D k : Nat} {header : Bits}
    {run generate : Bits → Option α} (fits : header.length + k ≤ D)
    (compiled : ∀ u : Bits, u.length = k → run (header ++ u) = generate u)
    (p : Bits) (y : α) :
    p ∈ fiber D k header run y ↔
      ∃ u : Bits, u.length = k ∧ p = header ++ u ∧ generate u = some y := by
  simp only [fiber, List.mem_filter, mem_names, Bool.and_eq_true,
    List.isPrefixOf_iff_prefix, decide_eq_true_eq]
  constructor
  · rintro ⟨hp, sel, hit⟩
    obtain ⟨u, hu, rfl⟩ := (selects_exactly_branch header p fits hp).1 sel
    exact ⟨u, hu, rfl, (compiled u hu).symm.trans hit⟩
  · rintro ⟨u, hu, rfl, hit⟩
    have hp : (header ++ u).length ≤ D := by simpa [hu] using fits
    exact ⟨hp, (selects_exactly_branch header _ fits hp).2 ⟨u, hu, rfl⟩,
      (compiled u hu).trans hit⟩

private theorem unique_length {α : Type} (ls : List α) (distinct : ls.Nodup)
    (unique : ∀ a ∈ ls, ∀ b ∈ ls, a = b) : ls.length ≤ 1 := by
  cases ls with
  | nil => simp
  | cons a tail =>
    cases tail with
    | nil => simp
    | cons b bs =>
      have same := unique a (by simp) b (by simp)
      exact False.elim ((List.nodup_cons.1 distinct).1 (by simp [same]))

/-- For a branch injective on successful outputs, selected parity is
    exactly the indicator of its range. All other branches can collide freely. -/
theorem parity_eq_image {α : Type} [DecidableEq α] {D k : Nat} {header : Bits}
    {run generate : Bits → Option α} (fits : header.length + k ≤ D)
    (compiled : ∀ u : Bits, u.length = k → run (header ++ u) = generate u)
    (injectiveOnHits : ∀ u v : Bits, ∀ y : α, u.length = k → v.length = k →
      generate u = some y → generate v = some y → u = v)
    (y : α) :
    (fiber D k header run y).length % 2 = 1 ↔
      ∃ u : Bits, u.length = k ∧ generate u = some y := by
  let f := fiber D k header run y
  have mem := fun p => mem_fiber fits compiled p y
  have distinct : f.Nodup := (names_distinct D).sublist (List.filter_sublist ..)
  have bound : f.length ≤ 1 := by
    apply unique_length f distinct
    intro a ha b hb
    obtain ⟨u, hu, rfl, hitU⟩ := (mem a).1 ha
    obtain ⟨v, hv, rfl, hitV⟩ := (mem b).1 hb
    rw [injectiveOnHits u v y hu hv hitU hitV]
  change f.length % 2 = 1 ↔ _
  constructor
  · intro odd
    have positive : 0 < f.length := by omega
    obtain ⟨p, hp⟩ := List.exists_mem_of_length_pos positive
    obtain ⟨u, hu, _, hit⟩ := (mem p).1 hp
    exact ⟨u, hu, hit⟩
  · rintro ⟨u, hu, hit⟩
    have hp : header ++ u ∈ f := (mem _).2 ⟨u, hu, rfl, hit⟩
    have positive := List.length_pos_of_mem hp
    omega

/-- Keep the output exactly when its halting time lies in (lo, hi]. -/
def inWindow {α : Type} (lo hi : Nat) : Option (Nat × α) → Option α
  | none => none
  | some (t,y) => if lo < t ∧ t ≤ hi then some y else none

theorem timed_parity_eq_image {α : Type} [DecidableEq α] {D k lo hi : Nat} {header : Bits}
    {run : Bits → Option (Nat × α)} {time : Bits → Nat} {generate : Bits → α}
    (fits : header.length + k ≤ D)
    (compiled : ∀ u : Bits, u.length = k → run (header ++ u) = some (time u, generate u))
    (injectiveAtWidth : ∀ u v : Bits, u.length = k → v.length = k →
      generate u = generate v → u = v) (y : α) :
    (fiber D k header (fun p => inWindow lo hi (run p)) y).length % 2 = 1 ↔
      ∃ u : Bits, u.length = k ∧ lo < time u ∧ time u ≤ hi ∧ generate u = y := by
  let event := fun u => inWindow lo hi (some (time u, generate u))
  have eventIff (u : Bits) (z : α) :
      event u = some z ↔ lo < time u ∧ time u ≤ hi ∧ generate u = z := by
    by_cases inside : lo < time u ∧ time u ≤ hi <;>
      simp [event, inWindow, inside, ← and_assoc]
  have agrees (u : Bits) (hu : u.length = k) :
      inWindow lo hi (run (header ++ u)) = event u := by rw [compiled u hu]
  have uniqueHits (u v : Bits) (z : α) (hu : u.length = k) (hv : v.length = k)
      (eu : event u = some z) (ev : event v = some z) : u = v :=
    injectiveAtWidth u v hu hv (((eventIff u z).1 eu).2.2.trans
      ((eventIff v z).1 ev).2.2.symm)
  rw [parity_eq_image fits agrees uniqueHits]
  simp only [eventIff]

end LiteralBranchParity
