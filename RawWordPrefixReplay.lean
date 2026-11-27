import Std

/-! A concrete execution on a fixed instruction path and its symbolic replay
where loads/stores/copies forward raw tags and numerical results are fixed.
Branch events certify that an actual program selects this path. -/
namespace RawWordPrefixReplay

inductive Atom (I V : Type) where
  | raw : I → Atom I V
  | fixed : V → Atom I V

def Atom.eval (theta : I → V) : Atom I V → V
  | .raw i => theta i
  | .fixed v => v

structure State (V T : Type) where
  reg : Nat → T
  mem : V → T

def State.map (f : T → U) (s : State V T) : State V U :=
  ⟨fun i => f (s.reg i), fun a => f (s.mem a)⟩

inductive Arg (V : Type) where
  | imm : V → Arg V
  | reg : Nat → Arg V

def readArg (lit : V → T) (s : State V T) : Arg V → T
  | .imm v => lit v
  | .reg i => s.reg i

inductive Instr (V : Type) where
  | load (dst : Nat) (addr : Arg V)
  | store (addr payload : Arg V)
  | copy (dst : Nat) (src : Arg V)
  | calc (dst : Nat) (op : V → V → V) (x y : Arg V)
  | branch (op : V → V → Bool) (x y : Arg V)

inductive Event (V : Type) where
  | quiet
  | address : V → Event V
  | numeric : V → Event V
  | branch : Bool → Event V

def observe (s : State V V) : Instr V → Event V
  | .load _ a | .store a _ => .address (readArg id s a)
  | .copy _ _ => .quiet
  | .calc _ op x y => .numeric (op (readArg id s x) (readArg id s y))
  | .branch op x y => .branch (op (readArg id s x) (readArg id s y))

def put [DecidableEq K] (f : K → T) (k : K) (v : T) : K → T :=
  fun j => if j = k then v else f j

/-- On the actual path the event always has the constructor prescribed by the instruction. -/
def update [DecidableEq V] (lit : V → T) (s : State V T) :
    Instr V → Event V → State V T
  | .load i _, .address a => {s with reg := put s.reg i (s.mem a)}
  | .store _ src, .address a => {s with mem := put s.mem a (readArg lit s src)}
  | .copy i src, .quiet => {s with reg := put s.reg i (readArg lit s src)}
  | .calc i _ _ _, .numeric v => {s with reg := put s.reg i (lit v)}
  | _, _ => s

theorem eval_update [DecidableEq V] (theta : I → V) (s : State V (Atom I V))
    (i : Instr V) (e : Event V) :
    (update Atom.fixed s i e).map (Atom.eval theta) =
       update id (s.map (Atom.eval theta)) i e := by
  have put_eq {K : Type} [DecidableEq K] (f : K → Atom I V) (k : K) (v : Atom I V) :
      (fun j => Atom.eval theta (put f k v j)) =
      put (fun j => Atom.eval theta (f j)) k (Atom.eval theta v) := by
    funext j
    by_cases h : j = k <;> simp [put,h]
  have arg_eq (a : Arg V) :
      Atom.eval theta (readArg Atom.fixed s a) = readArg id (s.map (Atom.eval theta)) a := by
    cases a <;> rfl
  cases i <;> cases e <;> simp only [update, State.map, State.mk.injEq, put_eq,
    true_and, and_true, and_self, arg_eq, id_eq] <;> try rfl
  all_goals first | exact arg_eq _ | rw [arg_eq] | rfl

def concrete [DecidableEq V] (s : State V V) :
    List (Instr V) → List (Event V) × State V V
  | [] => ([], s)
  | i :: tail =>
    let e := observe s i
    let (es, out) := concrete (update id s i e) tail
    (e :: es, out)

def symbolic [DecidableEq V] (center : I → V) (s : State V (Atom I V)) :
    List (Instr V) → List (Event V) × State V (Atom I V)
  | [] => ([], s)
  | i :: tail =>
    let e := observe (s.map (Atom.eval center)) i
    let (es, out) := symbolic center (update Atom.fixed s i e) tail
    (e :: es, out)

def guards [DecidableEq V] (center theta : I → V) (s : State V (Atom I V)) :
    List (Instr V) → Prop
  | [] => True
  | i :: tail =>
    let e := observe (s.map (Atom.eval center)) i
    observe (s.map (Atom.eval theta)) i = e ∧ guards center theta (update Atom.fixed s i e) tail

/-- All constrained numerical results, branch outcomes and addresses agree.
The actual final word array is exactly the tagged array evaluated at theta;
individual copied words need not have the center value. -/
theorem compatible_replay [DecidableEq V] (center theta : I → V)
    (path : List (Instr V)) (s : State V (Atom I V)) (ok : guards center theta s path) :
    concrete (s.map (Atom.eval theta)) path =
      ((symbolic center s path).1, (symbolic center s path).2.map (Atom.eval theta)) := by
  induction path generalizing s with
  | nil => rfl
  | cons i path ih =>
    obtain ⟨same,rest⟩ := ok
    simp only [concrete, symbolic, same, ← eval_update]
    rw [ih _ rest]

inductive Kind where
  | neither | firstRead | guard | both
  deriving DecidableEq

def discovery : Kind → Bool
  | .firstRead | .both => true
  | _ => false

def isGuard : Kind → Bool
  | .guard | .both => true
  | _ => false

def overlap : Kind → Bool
  | .both => true
  | _ => false

theorem dual_charge (xs : List Kind) :
    xs.countP discovery + xs.countP isGuard ≤ xs.length + xs.countP overlap := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    cases x <;> simp [List.countP_cons,discovery,isGuard,overlap] at * <;> omega

theorem suffix_loss (xs : List Kind) (j : Nat)
    (reads : j ≤ xs.countP discovery) (checks : j ≤ xs.countP isGuard)
    (one : xs.countP overlap ≤ 1) : j ≤ (xs.length+1)/2 := by
  have h := dual_charge xs
  omega

#print axioms compatible_replay
#print axioms suffix_loss

end RawWordPrefixReplay
