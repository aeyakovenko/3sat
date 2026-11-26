import Std

/-! Common intervals of two orders. Positions in the first order are their own
names; q gives their positions in the second. The seam criterion uses only
the local order properties needed by the diamond construction. -/
namespace SimplePermutationColoring

def ConvexIn {V : Type} (rank : V → Nat) (S : V → Prop) : Prop :=
  ∀ u v w, S u → S v → rank u ≤ rank w → rank w ≤ rank v → S w

private theorem monochrome_span {n : Nat}
    (side : Fin (n + 1) → Bool) (S : Fin (n + 1) → Prop)
    (convex : ConvexIn Fin.val S)
    (mono : ∀ u v, S u → S v → side u = side v)
    (noTriple : ∀ a b c, b.val = a.val + 1 → c.val = b.val + 1 →
      side a = side b → side b ≠ side c)
    (u v : Fin (n+1)) (hu : S u) (hv : S v) : v.val ≤ u.val + 1 := by
  apply Nat.le_of_not_gt
  intro h
  let b : Fin (n+1) := ⟨u.val+1, by omega⟩
  let c : Fin (n+1) := ⟨u.val+2, by omega⟩
  have hb : S b := convex u v b hu hv (by dsimp [b]; omega) (by dsimp [b]; omega)
  have hc : S c := convex u v c hu hv (by dsimp [c]; omega) (by dsimp [c]; omega)
  exact noTriple u b c rfl (by rfl) (mono u b hu hb) (mono b c hb hc)

/-- A second-order interval meeting both sides of the seam contains the two
extremes of the first order. A monochrome first-order interval has length at
most two; a separating second-order point excludes every pair of that size. -/
theorem singleton_or_whole {n : Nat} (q : Fin (n+1) → Nat)
    (side : Fin (n+1) → Bool) (x y : Fin (n+1))
    (extremes : ∀ v : Fin (n+1), x.val ≤ v.val ∧ v.val ≤ y.val)
    (seam : ∀ u v, side u = false → side v = true →
      q u ≤ q x ∧ q x ≤ q y ∧ q y ≤ q v)
    (noTriple : ∀ a b c, b.val = a.val + 1 → c.val = b.val + 1 →
      side a = side b → side b ≠ side c)
    (separate : ∀ a b, b.val = a.val + 1 → side a = side b →
      ∃ w, w ≠ a ∧ w ≠ b ∧
        (q a ≤ q w ∧ q w ≤ q b ∨ q b ≤ q w ∧ q w ≤ q a))
    (S : Fin (n+1) → Prop) (hp : ConvexIn Fin.val S) (hq : ConvexIn q S) :
    (∀ u v, S u → S v → u = v) ∨ (∀ v, S v) := by
  classical
  by_cases mixed : ∃ u v, S u ∧ S v ∧ side u = false ∧ side v = true
  · obtain ⟨u,v,hu,hv,lu,rv⟩ := mixed
    obtain ⟨a,b,c⟩ := seam u v lu rv
    have hx := hq u v x hu hv a (by omega)
    have hy := hq u v y hu hv (by omega) c
    exact Or.inr (fun w => hp x y w hx hy (extremes w).1 (extremes w).2)
  · have mono : ∀ u v, S u → S v → side u = side v := by
      intro u v hu hv
      cases a : side u <;> cases b : side v
      · rfl
      · exact False.elim (mixed ⟨u,v,hu,hv,a,b⟩)
      · exact False.elim (mixed ⟨v,u,hv,hu,b,a⟩)
      · rfl
    have span := monochrome_span side S hp mono noTriple
    have ordered : ∀ a b, S a → S b → a.val < b.val → False := by
      intro a b ha hb lt
      have step : b.val = a.val+1 := by have := span a b ha hb; omega
      obtain ⟨w,wa,wb,d⟩ := separate a b step (mono a b ha hb)
      have hw : S w := by
        rcases d with d | d
        · exact hq a b w ha hb d.1 d.2
        · exact hq b a w hb ha d.1 d.2
      have hw₁ := span a w ha hw
      have hw₂ := span w b hw hb
      have hone : w.val = a.val ∨ w.val = b.val := by omega
      rcases hone with h | h
      · exact wa (Fin.ext h)
      · exact wb (Fin.ext h)
    left
    intro u v hu hv
    apply Fin.ext
    change u.val = v.val
    have h₁ : ¬ u.val < v.val := ordered u v hu hv
    have h₂ : ¬ v.val < u.val := ordered v u hv hu
    omega

/-- Insert the new maximum at each position of every smaller permutation. -/
def orders : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => (orders n).flatMap fun p =>
      (List.range (n+1)).map fun i => p.take i ++ [n] ++ p.drop i

def simple (p : List Nat) : Bool :=
  (List.range p.length).all fun start =>
    (List.range p.length).all fun len =>
      if 2 ≤ len ∧ start + len ≤ p.length then
        let w := (p.drop start).take len
        (w.max?.getD 0 - w.min?.getD 0 + 1) != len
      else true

def assignments : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => (assignments n).flatMap fun colors => [0,1,2].map fun i => i :: colors

def proper : List Nat → Bool
  | a :: b :: rest => a != b && proper (b :: rest)
  | _ => true

def census (n : Nat) : Nat × Nat :=
  let candidates := (orders n).filter simple
  let alongFirst := (assignments n).filter proper
  (candidates.length, (candidates.filter (fun p => alongFirst.any fun color =>
    proper (p.map fun i => color[i]!))).length)

/-- Pair = (number of simple orders, number with a common proper 3-coloring). -/
theorem simple_orders_through_seven :
    census 4 = (2,0) ∧ census 5 = (6,6) ∧ census 6 = (46,46) ∧
    census 7 = (338,266) := by native_decide

/-- Insert a new first-order rank z at second-order slot j. -/
def insertPoint (p : List Nat) (j z : Nat) : List Nat :=
  let shifted := p.map fun x => if x < z then x else x+1
  shifted.take j ++ [z] ++ shifted.drop j

def hasColoring (p : List Nat) : Bool :=
  ((assignments p.length).filter proper).any fun c => proper (p.map fun i => c[i]!)

def uncolorableSimpleExtensions (p : List Nat) : Nat :=
  ((List.range (p.length+1)).flatMap (fun z =>
    (List.range (p.length+1)).map fun j => insertPoint p j z)).countP
      (fun q => simple q && !hasColoring q)

/-- A nontrivial obstruction to a one-point insertion preserving both
simplicity and the negative coloring verdict. -/
theorem seven_point_dead_end :
    let p := [1,3,5,2,6,0,4]
    simple p = true ∧ hasColoring p = false ∧
    uncolorableSimpleExtensions p = 0 := by native_decide

end SimplePermutationColoring
