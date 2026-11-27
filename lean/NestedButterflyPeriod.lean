import Std

/-! A product of unary bit maps with one exceptional configuration, and a
four-state machine driven by six-periodic input. -/

namespace NestedButterflyPeriod

def walk (F : Nat → α → α) (s : α) : Nat → α
  | 0 => s
  | n+1 => F n (walk F s n)

def itr (f : α → α) (n : Nat) (s : α) : α := walk (fun _ => f) s n

theorem bit_cube (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases ha : f false <;> cases hb : f true <;> cases x <;> simp_all

theorem product_cube {J : Type} (g : J → Bool → Bool) (v : J → Bool) :
    (fun j => g j (g j (g j (v j)))) = fun j => g j (v j) := by
  funext j
  exact bit_cube _ _

inductive Place where | a | b | c | d | e | f
  deriving DecidableEq

def ordinary : Place → Place
  | .a | .c => .b
  | .b => .c
  | .d | .f => .e
  | .e => .f

def next (hit : Place → Bool) (i : Place) : Place :=
  if hit i then .d else ordinary i

private theorem six_orbit (hit : Place → Bool) :
    itr (next hit) 10 .a = itr (next hit) 4 .a := by
  cases ha : hit .a <;> cases hb : hit .b <;> cases hc : hit .c <;>
    cases hd : hit .d <;> cases he : hit .e <;> cases hf : hit .f <;>
    simp [itr, walk, next, ordinary, ha,hb,hc,hd,he,hf]

def represent (z : α → α) (s u : α) : Place → α
  | .a => s | .b => z s | .c => z (z s)
  | .d => u | .e => z u | .f => z (z u)

theorem exceptional_row [DecidableEq α] (z : α → α) (s p u : α)
    (hz : ∀ a, z (z (z a)) = z a) :
    let step := fun a => if a = p then u else z a
    itr step 10 s = itr step 4 s := by
  let eval := represent z s u
  let hit := fun i => decide (eval i = p)
  let step := fun a => if a = p then u else z a
  have norm (i : Place) : eval (ordinary i) = z (eval i) := by
    cases i <;> simp [eval, represent, ordinary, hz]
  have one (i : Place) : eval (next hit i) = step (eval i) := by
    by_cases h : eval i = p
    · simp [next,hit,h,step]
      rfl
    · simp [next,hit,h,step,norm]
  have all (n : Nat) : eval (itr (next hit) n .a) = itr step n s := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change eval (next hit (itr (next hit) n .a)) = step (itr step n s)
      rw [one, ih]
  exact (all 10).symm.trans ((congrArg eval (six_orbit hit)).trans (all 4))

def lookup (a b c d : Fin 4) (x : Fin 4) : Fin 4 :=
  match x.val with | 0 => a | 1 => b | 2 => c | _ => d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem four_tables : ∀ a b c d x : Fin 4,
    itr (lookup a b c d) 15 x = itr (lookup a b c d) 3 x := by decide

theorem four_orbit (g : Fin 4 → Fin 4) (x : Fin 4) :
    itr g 15 x = itr g 3 x := by
  have h : g = lookup (g 0) (g 1) (g 2) (g 3) := by
    funext y
    obtain ⟨j,hj⟩ := y
    match j with
    | 0 | 1 | 2 | 3 => rfl
    | j+4 => omega
  exact (congrArg (fun f => itr f 15 x) h).trans ((four_tables _ _ _ _ _).trans
    (congrArg (fun f => itr f 3 x) h).symm)

def block (K : Nat → α → α) (n : Nat) (x : α) : α :=
  K (n+5) (K (n+4) (K (n+3) (K (n+2) (K (n+1) (K n x)))))

theorem driven_pair (K : Nat → Fin 4 → Fin 4) (s : Fin 4)
    (per : ∀ n, K (n+6) = K n) : walk K s 90 = walk K s 18 := by
  have phase (n : Nat) : block K (n+6) = block K n := by
    funext x
    simp [block, show n+6+5=n+5+6 by omega, show n+6+4=n+4+6 by omega,
      show n+6+3=n+3+6 by omega, show n+6+2=n+2+6 by omega, show n+6+1=n+1+6 by omega, per]
  have fixed (k : Nat) : block K (6*k) = block K 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simpa [Nat.mul_succ, phase] using ih
  have atBlock (k : Nat) : walk K s (6*k) = itr (block K 0) k s := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Nat.mul_succ]
      change block K (6*k) (walk K s (6*k)) = block K 0 _
      rw [fixed, ih]
      rfl
  exact (atBlock 15).trans ((four_orbit _ _).trans (atBlock 3).symm)

#print axioms exceptional_row
#print axioms driven_pair

end NestedButterflyPeriod
