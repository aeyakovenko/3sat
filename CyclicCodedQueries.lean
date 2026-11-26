import Std

/-! Directed edges, the positive and negative reachability certificates,
and a complement-invariant nonlinear change of the answer bits. -/
namespace CyclicCodedQueries

inductive Walk (edge : V → V → Prop) (s : V) : V → Prop
  | here : Walk edge s s
  | step {v w} : Walk edge s v → edge v w → Walk edge s w

structure Cut (edge : V → V → Prop) (s t : V) where
  inside : V → Prop
  source : inside s
  target : ¬ inside t
  forward : ∀ x y, edge x y → inside x → inside y

theorem cut_sound (c : Cut edge s t) : ¬ Walk edge s t := by
  intro path
  have propagated {v} (p : Walk edge s v) : c.inside v := by
    induction p with
    | here => exact c.source
    | step p e ih => exact c.forward _ _ e ih
  exact c.target (propagated path)

theorem absent_iff_cut : ¬ Walk edge s t ↔ Nonempty (Cut edge s t) := by
  constructor
  · exact fun banned => ⟨⟨Walk edge s, .here, banned, fun _ _ e p => .step p e⟩⟩
  · exact fun ⟨c⟩ => cut_sound c

/-- The local port counts of chosen arcs balance after injecting one unit at
the source and removing one at the target. -/
structure Flow (edge : V → V → Prop) (s t : V) where
  chosen : List (V × V)
  active : ∀ p ∈ chosen, edge p.1 p.2
  balance : (s :: chosen.map Prod.snd).Perm (t :: chosen.map Prod.fst)

private def mass (l : List V) (f : V → Nat) := (l.map f).sum

private theorem mass_perm {l r : List V} (h : l.Perm r) (f : V → Nat) :
    mass l f = mass r f := by
  induction h with
  | nil => rfl
  | cons x _ ih => simpa [mass] using congrArg (f x + ·) ih
  | swap x y zs => simp [mass, Nat.add_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem heads_dominate (l : List (V × V)) (f : V → Nat)
    (h : ∀ p ∈ l, f p.1 ≤ f p.2) :
    mass (l.map Prod.fst) f ≤ mass (l.map Prod.snd) f := by
  induction l with
  | nil => simp [mass]
  | cons p l ih =>
    have one := h p (by simp)
    have tail := ih (fun e he => h e (by simp [he]))
    simpa [mass] using Nat.add_le_add one tail

theorem flow_sound (w : Flow edge s t) : Walk edge s t := by
  classical
  apply Classical.byContradiction
  intro absent
  let c : Cut edge s t := ⟨Walk edge s, .here, absent, fun _ _ e p => .step p e⟩
  let f := fun v => if c.inside v then 1 else 0
  have mono := heads_dominate w.chosen f (fun p hp => by
    by_cases h : c.inside p.1
    · simp [f, h, c.forward _ _ (w.active p hp) h]
    · simp [f, h])
  have same := mass_perm w.balance f
  have src : f s = 1 := if_pos c.source
  have dst : f t = 0 := if_neg c.target
  change f s + mass (w.chosen.map Prod.snd) f =
    f t + mass (w.chosen.map Prod.fst) f at same
  omega

theorem walk_gives_flow (path : Walk edge s t) : Nonempty (Flow edge s t) := by
  induction path with
  | here => exact ⟨⟨[], by simp, .refl _⟩⟩
  | @step v t p e ih =>
    obtain ⟨prev⟩ := ih
    refine ⟨⟨(v,t) :: prev.chosen, ?_, ?_⟩⟩
    · intro a ha
      rcases List.mem_cons.mp ha with eq | tail
      · simpa [eq] using e
      · exact prev.active a tail
    · simp only [List.map_cons]
      exact (List.Perm.swap _ _ _).trans (prev.balance.cons t)

def painted (x : I → Bool) (b : Bool) : I → Bool := fun j => x j ^^ b

theorem painted_twice (x : I → Bool) (b : Bool) : painted (painted x b) b = x := by
  funext j
  unfold painted
  cases b <;> cases x j <;> rfl

theorem row_involution (h : (I → Bool) → Bool)
    (stable : ∀ x : I → Bool, h (painted x true) = h x) (x : I → Bool) :
    painted (painted x (h x)) (h (painted x (h x))) = x := by
  have hh : h (painted x (h x)) = h x := by
    cases val : h x with
    | false =>
      have neutral : painted x false = x := by funext j; unfold painted; cases x j <;> rfl
      rw [neutral, val]
    | true => exact (stable x).trans val
  rw [hh, painted_twice]

/-- A fixed set of predictions on a row leaves at most the prediction and
its complement as choices for the underlying answer bits on those sites. -/
theorem raw_from_painted {x : I → Bool} {j : A → I} {guess : A → Bool} {h : Bool}
    (correct : ∀ k, painted x h (j k) = guess k) :
    ∀ k, x (j k) = (guess k ^^ h) := by
  intro k
  rw [← correct k]
  unfold painted
  cases h <;> cases x (j k) <;> rfl

structure Group where
  c0 : Bool
  c1 : Bool
  p0 : Bool
  p1 : Bool
  q0 : Bool
  q1 : Bool

def Group.flip (g : Group) : Group :=
  ⟨!g.c0, !g.c1, !g.p0, !g.p1, !g.q0, !g.q1⟩

def Group.control (g : Group) : Bool := g.c0 ^^ g.c1

def Group.payload (g : Group) : Bool :=
  if g.control then g.q0 ^^ g.q1 else g.p0 ^^ g.p1

theorem control_flip (g : Group) : g.flip.control = g.control := by
  cases g.c0 <;> cases g.c1 <;> simp_all [Group.flip, Group.control]

private theorem flip_xor (x y : Bool) : ((!x) ^^ (!y)) = (x ^^ y) := by
  cases x <;> cases y <;> rfl

theorem payload_flip (g : Group) : g.flip.payload = g.payload := by
  unfold Group.payload
  rw [control_flip]
  cases g.control <;> apply flip_xor

def flags : List Group → Bool × Nat
  | [] => (false, 0)
  | g :: gs => let r := flags gs; (g.payload ^^ r.1, ((if g.control then 1 else 0) + r.2) % 3)

theorem flags_stable (gs : List Group) : flags (gs.map Group.flip) = flags gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [flags, ih, control_flip, payload_flip]

/-- Flipping the first bit of both payload pairs toggles exactly the selected
contribution. The selector and the accumulated residue are unchanged. -/
def Group.adjust (g : Group) (b : Bool) : Group :=
  {g with p0 := g.p0 ^^ b, q0 := g.q0 ^^ b}

theorem adjust_control (g : Group) (b : Bool) : (g.adjust b).control = g.control := rfl

theorem adjust_payload (g : Group) (b : Bool) : (g.adjust b).payload = (g.payload ^^ b) := by
  unfold Group.payload
  rw [adjust_control]
  cases g.control <;> simp only [Bool.false_eq_true, ↓reduceIte, Group.adjust]
  all_goals cases b <;> cases g.p0 <;> cases g.p1 <;> cases g.q0 <;> cases g.q1 <;> rfl

theorem two_fresh_controls (r : Fin 3) :
    ∃ b c : Nat, b ≤ 1 ∧ c ≤ 1 ∧ (b+c)%3 = r.val := by
  have bound := r.isLt
  by_cases zero : r.val = 0
  · exact ⟨0, 0, by decide, by decide, by omega⟩
  by_cases one : r.val = 1
  · exact ⟨1, 0, by decide, by decide, by omega⟩
  · exact ⟨1, 1, by decide, by decide, by omega⟩

end CyclicCodedQueries
