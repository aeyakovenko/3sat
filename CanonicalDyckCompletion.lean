import Std

/-! Canonical bounded suffixes for one stack, and a length-uniform
encoding of typed stack actions with skips into two types of brackets. -/
namespace CanonicalDyckCompletion

inductive Action (α : Type) where
  | push (x : α)
  | pop (x : α)
  | skip
  deriving DecidableEq

def step [DecidableEq α] : Action α → List α → Option (List α)
  | .push x, s => some (x :: s)
  | .pop _, [] => none
  | .pop x, y :: s => if x = y then some s else none
  | .skip, s => some s

def run [DecidableEq α] : List (Action α) → List α → Option (List α)
  | [], s => some s
  | e :: es, s => (step e s).bind (run es)

theorem run_append [DecidableEq α] (xs ys : List (Action α)) (s : List α) :
    run (xs ++ ys) s = (run xs s).bind (run ys) := by
  induction xs generalizing s with
  | nil => simp [run]
  | cons x xs ih => cases h : step x s <;> simp [run, h, ih]

theorem run_skips [DecidableEq α] (n : Nat) (s : List α) :
    run (List.replicate n .skip) s = some s := by
  induction n <;> simp_all [List.replicate_succ, run, step]

theorem run_pops_iff [DecidableEq α] (pops s tail : List α) :
    run (pops.map .pop) s = some tail ↔ s = pops ++ tail := by
  induction pops generalizing s with
  | nil => simp [run]
  | cons x xs ih =>
    cases s with
    | nil => simp [run, step]
    | cons y ys => by_cases eq : x = y <;> simp_all [run, step, eq_comm]

theorem run_pushes [DecidableEq α] (xs s : List α) :
    run (xs.map .push) s = some (xs.reverse ++ s) := by
  induction xs generalizing s with
  | nil => simp [run]
  | cons x xs ih => simp [run, step, ih, List.reverse_cons, List.append_assoc]

def completion (s : List α) (n : Nat) : List (Action α) :=
  s.map .pop ++ List.replicate (n - s.length) .skip

def suffixShape (xs : List (Action α)) : Prop :=
  ∃ (pops : List α) (k : Nat), xs = pops.map .pop ++ List.replicate k .skip

/-- The stack is listed from top to bottom. If it is too deep, no such
suffix exists. Otherwise the exact event sequence is forced. -/
theorem completion_iff [DecidableEq α] (s : List α) (n : Nat) (xs : List (Action α)) :
    (xs.length = n ∧ suffixShape xs ∧ run xs s = some []) ↔
    s.length ≤ n ∧ xs = completion s n := by
  constructor
  · rintro ⟨len, ⟨pops, k, rfl⟩, done⟩
    rw [run_append] at done
    cases h : run (pops.map .pop) s with
    | none => simp [h] at done
    | some t =>
      have ht : t = [] := by simpa [h, run_skips] using done
      subst t
      have hs : s = pops := by simpa using (run_pops_iff pops s []).mp h
      subst s
      simp at len
      have hk : n - pops.length = k := by omega
      exact ⟨by omega, by simp [completion, hk]⟩
  · rintro ⟨len, rfl⟩
    refine ⟨?_, ⟨s, n - s.length, rfl⟩, ?_⟩
    · simp [completion]
      omega
    · rw [completion, run_append, (run_pops_iff s s []).mpr (by simp)]
      simp [run_skips]

theorem height_bound [DecidableEq α] (xs : List (Action α)) (s t : List α)
    (h : run xs s = some t) : t.length ≤ s.length + xs.length := by
  induction xs generalizing s with
  | nil => simp_all [run]
  | cons x xs ih =>
    cases op : step x s with
    | none => simp [run, op] at h
    | some s' =>
      have ht := ih s' (by simpa [run, op] using h)
      have hs : s'.length ≤ s.length + 1 := by
        cases x with
        | skip => simp_all [step]
        | push x =>
          have eq : x :: s = s' := Option.some.inj op
          rw [← eq]
          simp
        | pop x =>
          cases s with
          | nil => simp [step] at op
          | cons y ys => by_cases eq : x = y <;> simp_all [step] <;> omega
      simp only [List.length_cons]
      omega

/-- A legal observed trace can always be completed in exactly its own
length; a suffix satisfying the pop-then-skip condition is unique. -/
theorem trace_completion [DecidableEq α] (trace : List (Action α)) (s : List α)
    (ok : run trace [] = some s) (suffix : List (Action α)) :
    (suffix.length = trace.length ∧ suffixShape suffix ∧ run (trace ++ suffix) [] = some []) ↔
    suffix = completion s trace.length := by
  have hs : s.length ≤ trace.length := by simpa using height_bound trace [] s ok
  simpa [run_append, ok, hs] using completion_iff s trace.length suffix

inductive Bracket where
  | openBit (b : Bool)
  | closeBit (b : Bool)

def asAction : Bracket → Action Bool
  | .openBit b => .push b
  | .closeBit b => .pop b

def doubled (code : α → List Bool) (x : α) := code x ++ code x

def packedStack (code : α → List Bool) (s : List α) := s.flatMap (doubled code)

def neutral : List Bracket := [.openBit false, .closeBit false]

def encode (code : α → List Bool) (b : Nat) : Action α → List Bracket
  | .push x => (doubled code x).reverse.map .openBit
  | .pop x => (doubled code x).map .closeBit
  | .skip => (List.replicate b neutral).flatten

theorem neutral_run (b : Nat) (s : List Bool) :
    run (((List.replicate b neutral).flatten).map asAction) s = some s := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    simp [List.replicate_succ, neutral, asAction, run, step, neutral] at *
    exact ih

theorem encoded_length (code : α → List Bool) (b : Nat) (size : ∀ x, (code x).length = b)
    (a : Action α) : (encode code b a).length = 2*b := by
  cases a with
  | push x => simp [encode, doubled, size, Nat.two_mul]
  | pop x => simp [encode, doubled, size, Nat.two_mul]
  | skip =>
    induction b with
    | zero => simp [encode]
    | succ b ih =>
      simp only [encode, List.replicate_succ, List.flatten_cons, List.length_append] at *
      simp [neutral, Nat.mul_succ]
      omega

private theorem block_injective (code : α → List Bool) (b : Nat)
    (size : ∀ x, (code x).length = b)
    (unique : ∀ {x y}, code x = code y → x = y) {x y : α}
    (eq : doubled code x = doubled code y) : x = y :=
  unique (List.append_inj_left eq ((size x).trans (size y).symm))

theorem encoded_step [DecidableEq α] (code : α → List Bool) (b : Nat) (positive : 0 < b)
    (size : ∀ x, (code x).length = b) (unique : ∀ {x y}, code x = code y → x = y)
    (a : Action α) (s : List α) :
    run ((encode code b a).map asAction) (packedStack code s) =
    (step a s).map (packedStack code) := by
  cases a with
  | skip => exact neutral_run b _
  | push x =>
    change run (((doubled code x).reverse.map Bracket.openBit).map asAction) _ = _
    rw [List.map_map]
    change run ((doubled code x).reverse.map Action.push) _ = _
    rw [run_pushes, List.reverse_reverse]
    rfl
  | pop x =>
    change run (((doubled code x).map Bracket.closeBit).map asAction) _ = _
    rw [List.map_map]
    change run ((doubled code x).map Action.pop) _ = _
    cases s with
    | nil =>
      change run ((doubled code x).map Action.pop) [] = none
      cases hr : run ((doubled code x).map Action.pop) [] with
      | none => rfl
      | some t =>
        have hw := congrArg List.length ((run_pops_iff _ _ _).mp hr)
        simp [doubled, size] at hw
        omega
    | cons y ys =>
      change run ((doubled code x).map Action.pop) (doubled code y ++ packedStack code ys) = _
      by_cases eq : x = y
      · subst y
        simpa [step] using (run_pops_iff (doubled code x)
          (doubled code x ++ packedStack code ys) (packedStack code ys)).mpr rfl
      · simp only [step, if_neg eq, Option.map_none]
        cases hr : run ((doubled code x).map Action.pop) (doubled code y ++ packedStack code ys) with
        | none => rfl
        | some t =>
          have blocks := List.append_inj_left ((run_pops_iff _ _ _).mp hr)
            (show (doubled code y).length = (doubled code x).length by simp [doubled, size])
          exact False.elim (eq (block_injective code b size unique blocks.symm))

theorem encoded_trace [DecidableEq α] (code : α → List Bool) (b : Nat) (positive : 0 < b)
    (size : ∀ x, (code x).length = b) (unique : ∀ {x y}, code x = code y → x = y)
    (xs : List (Action α)) (s : List α) :
    run ((xs.flatMap (encode code b)).map asAction) (packedStack code s) =
    (run xs s).map (packedStack code) := by
  induction xs generalizing s with
  | nil => simp [run]
  | cons x xs ih =>
    rw [List.flatMap_cons, List.map_append, run_append,
      encoded_step code b positive size unique, run]
    cases h : step x s <;> simp [ih]

theorem encoded_dyck_iff [DecidableEq α] (code : α → List Bool) (b : Nat) (positive : 0 < b)
    (size : ∀ x, (code x).length = b) (unique : ∀ {x y}, code x = code y → x = y)
    (xs : List (Action α)) :
    run ((xs.flatMap (encode code b)).map asAction) [] = some [] ↔ run xs [] = some [] := by
  change run _ (packedStack code []) = some [] ↔ _
  rw [encoded_trace code b positive size unique]
  cases hr : run xs [] with
  | none => simp
  | some s =>
    cases s with
    | nil => simp [packedStack]
    | cons x xs =>
      have hn : doubled code x ≠ [] := by
        intro e
        have len := congrArg List.length e
        simp [doubled, size] at len
        omega
      simp [packedStack, hn]

theorem trace_encoded_length (code : α → List Bool) (b : Nat)
    (size : ∀ x, (code x).length = b) (xs : List (Action α)) :
    (xs.flatMap (encode code b)).length = 2*b*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [encoded_length code b size, ih, Nat.mul_succ, Nat.add_comm]

def isOpen : Bracket → Bool
  | .openBit _ => true
  | .closeBit _ => false

def bit : Bracket → Bool
  | .openBit v | .closeBit v => v

private theorem neutral_opens (b : Nat) :
    ((List.replicate b neutral).flatten).countP isOpen = b := by
  induction b with
  | zero => simp
  | succ b ih => simp [List.replicate_succ, neutral, isOpen] at *

private theorem encoded_opens (code : α → List Bool) (b : Nat)
    (size : ∀ x, (code x).length = b) (a : Action α) :
    (encode code b a).countP isOpen = match a with
      | .push _ => 2*b | .pop _ => 0 | .skip => b := by
  cases a with
  | push x =>
    rw [encode, List.countP_map]
    change (List.countP (fun _ => true) _) = _
    simp [doubled, size, Nat.two_mul]
  | pop x =>
    rw [encode, List.countP_map]
    change (List.countP (fun _ => false) _) = _
    simp
  | skip => exact neutral_opens _

theorem encode_injective (code : α → List Bool) (b : Nat) (positive : 0 < b)
    (size : ∀ x, (code x).length = b) (unique : ∀ {x y}, code x = code y → x = y)
    {a a' : Action α} (h : encode code b a = encode code b a') : a = a' := by
  have counts := congrArg (List.countP isOpen) h
  simp only [encoded_opens code b size] at counts
  have bits := congrArg (List.map bit) h
  cases a <;> cases a' <;> simp only at counts <;> try rfl
  case push.push x y =>
    have rev : (doubled code x).reverse = (doubled code y).reverse := by
      simpa only [encode, List.map_map, show bit ∘ Bracket.openBit = id from rfl, List.map_id]
        using bits
    exact congrArg Action.push (block_injective code b size unique (List.reverse_inj.mp rev))
  case pop.pop x y =>
    have same : doubled code x = doubled code y := by
      simpa only [encode, List.map_map, show bit ∘ Bracket.closeBit = id from rfl, List.map_id]
        using bits
    exact congrArg Action.pop (block_injective code b size unique same)
  all_goals exact False.elim (by omega)

/-- Parsimony at the level of source words: distinct action sequences
give distinct binary bracket words, even without supplied boundary markers. -/
theorem trace_encode_injective (code : α → List Bool) (b : Nat) (positive : 0 < b)
    (size : ∀ x, (code x).length = b) (unique : ∀ {x y}, code x = code y → x = y)
    {xs ys : List (Action α)} (eq : xs.flatMap (encode code b) = ys.flatMap (encode code b)) :
    xs = ys := by
  have len : ∀ z, (encode code b z).length = 2*b := encoded_length code b size
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons z zs =>
      have lengths := congrArg List.length eq
      simp [len] at lengths
      omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      have lengths := congrArg List.length eq
      simp [len] at lengths
      omega
    | cons z zs =>
      obtain ⟨head, tail⟩ := List.append_inj eq ((len x).trans (len z).symm)
      rw [encode_injective code b positive size unique head, ih tail]

end CanonicalDyckCompletion
