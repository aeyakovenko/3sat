import Std

namespace ModularNoisyGateEvaluation

/-- Only the semiring laws used in a two-state channel and cube contraction. -/
class Weights (R : Type) extends Add R, Mul R, Zero R, OfNat R 1 where
  add_assoc (x y z : R) : x + y + z = x + (y + z)
  add_comm (x y : R) : x + y = y + x
  add_zero (x : R) : x + 0 = x
  mul_assoc (x y z : R) : x * y * z = x * (y * z)
  mul_comm (x y : R) : x * y = y * x
  one_mul (x : R) : 1 * x = x
  zero_mul (x : R) : 0 * x = 0
  distrib (x y z : R) : x * (y + z) = x*y + x*z

structure Channel (R : Type) where
  keep : R
  flip : R

def entry (p : Channel R) (x y : Bool) := if x == y then p.keep else p.flip

def compose [Weights R] (p q : Channel R) : Channel R :=
  ⟨p.keep*q.keep + p.flip*q.flip, p.keep*q.flip + p.flip*q.keep⟩

theorem matrix_product [Weights R] (p q : Channel R) (x y : Bool) :
    entry p x false * entry q false y + entry p x true * entry q true y =
      entry (compose p q) x y := by
  cases x <;> cases y <;> simp [entry, compose, Weights.add_comm]

private theorem right_distrib [Weights R] (x y z : R) : (x+y)*z = x*z + y*z := by
  rw [Weights.mul_comm (x+y), Weights.distrib, Weights.mul_comm z x, Weights.mul_comm z y]

theorem paired_identity [Weights R] (charTwo : ∀ x : R, x+x=0)
    (p : Channel R) (norm : p.keep+p.flip=1) :
    compose p p = ⟨1,0⟩ := by
  have cross : p.keep*p.flip + p.flip*p.keep = 0 := by
    rw [Weights.mul_comm p.flip p.keep, charTwo]
  have sq : (p.keep+p.flip)*(p.keep+p.flip) = 1 := by
    rw [norm, Weights.one_mul]
  rw [right_distrib, Weights.distrib, Weights.distrib] at sq
  have group : p.keep*p.keep+p.keep*p.flip+(p.flip*p.keep+p.flip*p.flip) =
      (p.keep*p.keep+p.flip*p.flip)+(p.keep*p.flip+p.flip*p.keep) := by
    simp only [Weights.add_assoc, Weights.add_comm, show ∀ a b c : R, a+(b+c)=b+(a+c) by
      intro a b c; rw [← Weights.add_assoc, Weights.add_comm a b, Weights.add_assoc]]
  rw [group, cross, Weights.add_zero] at sq
  simp [compose, sq, cross]

/-- Evaluate Boolean leaf values by weighting independent residual bits. -/
def weighted [Weights R] : List (Channel R) → (List Bool → R) → R
  | [], f => f []
  | c::cs, f =>
    c.keep * weighted cs (fun x => f (false::x)) +
    c.flip * weighted cs (fun x => f (true::x))

/-- A gate and its identity buffer expose only the XOR of their fault bits. -/
def blocks [Weights R] : List (Channel R × Channel R) → (List Bool → R) → R
  | [], f => f []
  | (p,q)::cs, f =>
    let no := blocks cs (fun x => f (false::x))
    let yes := blocks cs (fun x => f (true::x))
    p.keep*(q.keep*no + q.flip*yes) + p.flip*(q.keep*yes + q.flip*no)

private theorem regroup [Weights R] (x y z w : R) : x+y+(z+w) = x+w+(y+z) := by
  simp only [Weights.add_assoc, Weights.add_comm, show ∀ a b c : R, a+(b+c)=b+(a+c) by
    intro a b c; rw [← Weights.add_assoc, Weights.add_comm a b, Weights.add_assoc]]

theorem collapse [Weights R] (cs : List (Channel R × Channel R)) (f : List Bool → R) :
    blocks cs f = weighted (cs.map (fun pq => compose pq.1 pq.2)) f := by
  induction cs generalizing f with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨p,q⟩ := pair
    simp only [blocks, List.map_cons, weighted, compose, ih, Weights.distrib, right_distrib,
      Weights.mul_assoc]
    exact regroup _ _ _ _

theorem diagonal [Weights R] (cs : List (Channel R)) (f : List Bool → R)
    (norm : ∀ p ∈ cs, p.keep+p.flip=1) (charTwo : ∀ x : R, x+x=0) :
    blocks (cs.map (fun p => (p,p))) f = f (List.replicate cs.length false) := by
  rw [collapse]
  induction cs generalizing f with
  | nil => rfl
  | cons p cs ih =>
    have comp := paired_identity charTwo p (norm p (by simp))
    have tail := ih (fun x => f (false::x)) (fun h mem => norm h (by simp [mem]))
    simp only [List.map_cons, List.length_cons, weighted, comp, Weights.one_mul,
      Weights.zero_mul, Weights.add_zero, List.replicate_succ]
    exact tail

/-- Integer form of the ternary lifting factor (1+3u)^2+(1+3u)+1. -/
theorem cube_lift (u : Nat) :
    (1+3*u)*(1+3*u)+(1+3*u)+1 = 3*(1+3*(u+u*u)) := by
  simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  omega

theorem ternary_depth (t : Nat) :
    ∃ u : Nat, 2^(2*3^t) = 1 + 3^(t+1)*u ∧ u%3=1 := by
  induction t with
  | zero => exact ⟨1, by decide, by decide⟩
  | succ t ih =>
    obtain ⟨u, eq, unit⟩ := ih
    let v := 3^t*u
    have rep : 3^(t+1)*u = 3*v := by
      simp only [Nat.pow_succ, v]
      ac_rfl
    have geom (w : Nat) : (1+w)^3 = 1+w*((1+w)*(1+w)+(1+w)+1) := by
      simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
      omega
    have cubed : (1+3*v)^3 = 1+9*v*(1+3*(v+v*v)) := by
      rw [geom, cube_lift]
      change 1 + 3*v*(3*(1+3*(v+v*v))) = 1+(3*3)*v*(1+3*(v+v*v))
      congr 1
      ac_rfl
    refine ⟨u*(1+3*(v+v*v)), ?_, ?_⟩
    · have step : 2 * 3^(t+1) = (2*3^t)*3 := by rw [Nat.pow_succ, Nat.mul_assoc]
      rw [step, Nat.pow_mul, eq, rep, cubed]
      congr 1
      simp only [Nat.pow_succ, v]
      calc
        _ = (3*3) * (3^t*u) * (1 + 3*(3^t*u + 3^t*u*(3^t*u))) := rfl
        _ = _ := by ac_rfl
    · simp [Nat.mul_mod, Nat.add_mod, unit]

end ModularNoisyGateEvaluation
