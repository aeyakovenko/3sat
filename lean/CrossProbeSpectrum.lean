import Std

namespace CrossProbeSpectrum

/-- A repeated coordinate in a monomial contributes its sign again. -/
def char (x : Nat → Bool) (i : Nat) : Int := if x i then -1 else 1

def monomial (x : Nat → Bool) : List Nat → Int
  | [] => 1
  | i :: is => char x i * monomial x is

abbrev Poly := List (Int × List Nat)

def eval (x : Nat → Bool) : Poly → Int
  | [] => 0
  | (c,is) :: ps => c * monomial x is + eval x ps

def signedLift (a : Int) (i : Nat) (ps : Poly) : Poly :=
  ps.map (fun (c,is) => (a*c, i::is))

theorem eval_append (x) (ps qs : Poly) : eval x (ps++qs) = eval x ps + eval x qs := by
  induction ps with
  | nil => simp [eval]
  | cons p ps ih =>
    rcases p with ⟨c,is⟩
    simp [eval, ih, Int.add_assoc]

theorem eval_lift (x) (a i) (ps : Poly) :
    eval x (signedLift a i ps) = (a * char x i) * eval x ps := by
  induction ps with
  | nil => simp [eval, signedLift]
  | cons p ps ih =>
    rcases p with ⟨c,is⟩
    change a*c * (char x i * monomial x is) + eval x (signedLift a i ps) =
      a * char x i * (c * monomial x is + eval x ps)
    rw [ih, Int.mul_add]
    ac_rfl

inductive Tree where
  | leaf (value : Int)
  | query (index : Nat) (zero one : Tree)

def run (x : Nat → Bool) : Tree → Int
  | .leaf k => k
  | .query i z o => if x i then run x o else run x z

def depth : Tree → Nat
  | .leaf _ => 0
  | .query _ z o => 1 + max (depth z) (depth o)

def degreeLE (d : Nat) (ps : Poly) : Prop := ∀ p ∈ ps, p.2.length ≤ d

theorem expansion (t : Tree) (d : Nat) (fits : depth t ≤ d) :
    ∃ ps : Poly, degreeLE d ps ∧ ∀ x, eval x ps = (2:Int)^d * run x t := by
  induction t generalizing d with
  | leaf k =>
    refine ⟨[((2:Int)^d*k, [])], ?_, ?_⟩
    · intro p hp
      simp at hp
      simp [hp]
    · intro x
      simp [eval, monomial, run]
  | query i z o iz io =>
    cases d with
    | zero => simp [depth] at fits
    | succ d =>
      have hz : depth z ≤ d := by have := Nat.le_max_left (depth z) (depth o); simp [depth] at fits; omega
      have ho : depth o ≤ d := by have := Nat.le_max_right (depth z) (depth o); simp [depth] at fits; omega
      obtain ⟨P,hP,eP⟩ := iz d hz
      obtain ⟨Q,hQ,eQ⟩ := io d ho
      refine ⟨(P ++ signedLift 1 i P) ++ (Q ++ signedLift (-1) i Q), ?_, ?_⟩
      · intro p hp
        simp only [List.mem_append, signedLift, List.mem_map] at hp
        rcases hp with ((h | ⟨a,ha,rfl⟩) | (h | ⟨a,ha,rfl⟩))
        · exact Nat.le_succ_of_le (hP p h)
        · exact Nat.succ_le_succ (hP a ha)
        · exact Nat.le_succ_of_le (hQ p h)
        · exact Nat.succ_le_succ (hQ a ha)
      · intro x
        rw [eval_append, eval_append, eval_append, eval_lift, eval_lift, eP, eQ]
        rw [Int.pow_succ, Int.mul_comm ((2:Int)^d) 2]
        cases h : x i <;> simp [char, run, h, Int.mul_assoc] <;> omega

/-- A cell of a sound cut has only correct successful outputs. -/
theorem sound_cell (truth : Bool) (active : Bool) (ans : Option Bool)
    (valid : active = true → ∀ b, ans = some b → b = truth) :
    (if active then (match ans with | none => (0:Int) | some b => if b = truth then 1 else -1) else 0)
      = (if active && ans.isSome then 1 else 0) := by
  cases active <;> cases ans <;> simp_all

theorem coverage (events : List (List Nat)) (cap : Nat)
    (perEvent : ∀ e ∈ events, e.length ≤ cap) : events.flatten.length ≤ events.length * cap := by
  induction events with
  | nil => simp
  | cons e es ih =>
    have h := perEvent e (by simp)
    have rest := ih (by intro a ha; exact perEvent a (by simp [ha]))
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

end CrossProbeSpectrum
