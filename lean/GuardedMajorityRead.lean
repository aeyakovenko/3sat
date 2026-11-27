import Std

/-! Boolean semantics for guarded majority witnesses, and the pivotal final leaf
in a fully exposed short-circuit evaluation. -/
namespace GuardedMajorityRead

def majority (a b c : Bool) : Bool :=
  if a == b then a else c

def pairs (a b c : Bool) : Bool := (a || b) && (a || c) && (b || c)

theorem majority_eq_pairs (a b c : Bool) : majority a b c = pairs a b c := by
  cases a <;> cases b <;> cases c <;> decide

theorem majority_mono {a b c A B C : Bool}
    (ha : a = true → A = true) (hb : b = true → B = true)
    (hc : c = true → C = true) :
    majority a b c = true → majority A B C = true := by
  cases a <;> cases b <;> cases c <;> cases A <;> cases B <;> cases C <;>
    simp_all [majority]

inductive Tree where
  | leaf (value : Bool)
  | node (first second third : Tree)

def value : Tree → Bool
  | .leaf b => b
  | .node a b c => majority (value a) (value b) (value c)

/-- A choice of activation bits for a complete canonical data assignment.
The three ternary gate clauses demand the pair conditions when active. -/
def allowed : Tree → Bool → Prop
  | .leaf b, active => active = true → b = true
  | .node a b c, active =>
    ∃ x y z : Bool, allowed a x ∧ allowed b y ∧ allowed c z ∧
      (active = true → pairs x y z = true)

theorem inactive (t : Tree) : allowed t false := by
  induction t with
  | leaf b => simp [allowed]
  | node a b c ha hb hc =>
    exact ⟨false,false,false,ha,hb,hc,by simp⟩

theorem active_iff (t : Tree) : allowed t true ↔ value t = true := by
  induction t with
  | leaf b => simp [allowed,value]
  | node a b c ha hb hc =>
    constructor
    · rintro ⟨x,y,z,hx,hy,hz,gate⟩
      apply majority_mono (a := x) (b := y) (c := z)
      · intro ex; exact ha.mp (ex ▸ hx)
      · intro ey; exact hb.mp (ey ▸ hy)
      · intro ez; exact hc.mp (ez ▸ hz)
      · rw [majority_eq_pairs]; exact gate rfl
    · intro yes
      have choose (u : Tree) (hu : allowed u true ↔ value u = true) :
          allowed u (value u) := by
        cases h : value u with
        | false => exact inactive u
        | true => exact hu.mpr h
      exact ⟨value a,value b,value c,choose a ha,choose b hb,choose c hc,
        fun _ => (majority_eq_pairs ..) ▸ yes⟩

/-- All leaves of all children are read, and the third one is needed. -/
def full : Tree → Prop
  | .leaf _ => True
  | .node a b c => full a ∧ full b ∧ full c ∧ value a ≠ value b

def flipFinal : Tree → Tree
  | .leaf b => .leaf (!b)
  | .node a b c => .node a b (flipFinal c)

theorem full_flip (t : Tree) (h : full t) :
    full (flipFinal t) ∧ value (flipFinal t) = !(value t) := by
  induction t with
  | leaf b => exact ⟨trivial,rfl⟩
  | node a b c _ _ ih =>
    obtain ⟨h₁,h₂,h₃,diff⟩ := h
    obtain ⟨recFull,recChange⟩ := ih h₃
    refine ⟨⟨h₁,h₂,recFull,diff⟩,?_⟩
    simpa [value,flipFinal,majority,diff] using recChange

/-- The four-child operation used in the stronger construction. -/
def gate4 (a b c d : Bool) := (a && b) || (c && d)

theorem gate4_guard (a b c d : Bool) :
    gate4 a b c d = ((a || c) && (a || d) && (b || c) && (b || d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

def lastOutcome (a b c d : Bool) : Bool × Nat :=
  if a then
    if b then (true,2)
    else if c then (d,4) else (false,3)
  else if c then (d,3) else (false,2)

theorem gate4_full_iff (a b c d : Bool) :
    (lastOutcome a b c d).2 = 4 ↔ a = true ∧ b = false ∧ c = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem gate4_value (a b c d : Bool) : (lastOutcome a b c d).1 = gate4 a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem gate4_last_flip (a b c d : Bool) (h : (lastOutcome a b c d).2 = 4) :
    gate4 a b c (!d) = !(gate4 a b c d) := by
  obtain ⟨rfl,rfl,rfl⟩ := (gate4_full_iff ..).mp h
  rfl

end GuardedMajorityRead
