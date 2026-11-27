import Std

namespace OnePointStrip18

def blue : List Nat := [16, 8, 5, 3, 13, 4, 2, 10, 17, 15, 0, 9, 11, 6, 12, 7, 14, 1]

def marks : List (Nat × Nat) := [(13,14),(8,5),(15,0)]

def path (p : List Nat) := p.zip p.tail

def edges := ((path (List.range 18)) ++ path blue).filter (fun e => !(marks.contains e))

def Proper (h : Nat → Fin 3) := ∀ e ∈ edges, h e.1 ≠ h e.2

private theorem diamond : ∀ p q s t : Fin 3, p ≠ q → s ≠ p → s ≠ q →
    t ≠ p → t ≠ q → s = t := by decide

/-- The three indicated groups exhaust the palette on every admissible boundary. -/
theorem forced (h : Nat → Fin 3) (H : Proper h) :
    h 13 = h 5 ∧ h 13 = h 0 ∧ h 8 = h 15 ∧
    h 13 ≠ h 14 ∧ h 13 ≠ h 8 ∧ h 14 ≠ h 8 := by
  have e5 : h 5 = h 2 := diamond (h 3) (h 4) (h 5) (h 2)
    (by simpa only [] using (H (3,4) (by decide)))
    (by simpa only [] using (H (5,3) (by decide)))
    (by simpa only [] using (Ne.symm (H (4,5) (by decide))))
    (by simpa only [] using (H (2,3) (by decide)))
    (by simpa only [] using (Ne.symm (H (4,2) (by decide))))
  have e13 : h 13 = h 2 := diamond (h 3) (h 4) (h 13) (h 2)
    (by simpa only [e5] using (H (3,4) (by decide)))
    (by simpa only [e5] using (Ne.symm (H (3,13) (by decide))))
    (by simpa only [e5] using (H (13,4) (by decide)))
    (by simpa only [e5] using (H (2,3) (by decide)))
    (by simpa only [e5] using (Ne.symm (H (4,5) (by decide))))
  have e7 : h 7 = h 2 := diamond (h 6) (h 12) (h 7) (h 2)
    (by simpa only [e5, e13] using (H (6,12) (by decide)))
    (by simpa only [e5, e13] using (Ne.symm (H (6,7) (by decide))))
    (by simpa only [e5, e13] using (Ne.symm (H (12,7) (by decide))))
    (by simpa only [e5, e13] using (H (5,6) (by decide)))
    (by simpa only [e5, e13] using (Ne.symm (H (12,13) (by decide))))
  have e11 : h 11 = h 2 := diamond (h 6) (h 12) (h 11) (h 2)
    (by simpa only [e5, e13, e7] using (H (6,12) (by decide)))
    (by simpa only [e5, e13, e7] using (H (11,6) (by decide)))
    (by simpa only [e5, e13, e7] using (H (11,12) (by decide)))
    (by simpa only [e5, e13, e7] using (H (5,6) (by decide)))
    (by simpa only [e5, e13, e7] using (Ne.symm (H (12,13) (by decide))))
  have e10 : h 10 = h 8 := diamond (h 2) (h 9) (h 10) (h 8)
    (by simpa only [e5, e13, e7, e11] using (Ne.symm (H (9,11) (by decide))))
    (by simpa only [e5, e13, e7, e11] using (H (10,11) (by decide)))
    (by simpa only [e5, e13, e7, e11] using (Ne.symm (H (9,10) (by decide))))
    (by simpa only [e5, e13, e7, e11] using (Ne.symm (H (7,8) (by decide))))
    (by simpa only [e5, e13, e7, e11] using (H (8,9) (by decide)))
  have e15 : h 15 = h 8 := diamond (h 16) (h 17) (h 15) (h 8)
    (by simpa only [e5, e13, e7, e11, e10] using (H (16,17) (by decide)))
    (by simpa only [e5, e13, e7, e11, e10] using (H (15,16) (by decide)))
    (by simpa only [e5, e13, e7, e11, e10] using (Ne.symm (H (17,15) (by decide))))
    (by simpa only [e5, e13, e7, e11, e10] using (Ne.symm (H (16,8) (by decide))))
    (by simpa only [e5, e13, e7, e11, e10] using (H (10,17) (by decide)))
  have e8 : h 8 = h 1 := diamond (h 2) (h 14) (h 8) (h 1)
    (by simpa only [e5, e13, e7, e11, e10, e15] using (H (7,14) (by decide)))
    (by simpa only [e5, e13, e7, e11, e10, e15] using (Ne.symm (H (7,8) (by decide))))
    (by simpa only [e5, e13, e7, e11, e10, e15] using (Ne.symm (H (14,15) (by decide))))
    (by simpa only [e5, e13, e7, e11, e10, e15] using (H (1,2) (by decide)))
    (by simpa only [e5, e13, e7, e11, e10, e15] using (Ne.symm (H (14,1) (by decide))))
  have e2 : h 2 = h 0 := diamond (h 1) (h 9) (h 2) (h 0)
    (by simpa only [e5, e13, e7, e11, e10, e15, e8] using (H (8,9) (by decide)))
    (by simpa only [e5, e13, e7, e11, e10, e15, e8] using (Ne.symm (H (1,2) (by decide))))
    (by simpa only [e5, e13, e7, e11, e10, e15, e8] using (Ne.symm (H (9,11) (by decide))))
    (by simpa only [e5, e13, e7, e11, e10, e15, e8] using (H (0,1) (by decide)))
    (by simpa only [e5, e13, e7, e11, e10, e15, e8] using (H (0,9) (by decide)))
  simp only [e5, e13, e7, e11, e10, e15, e8, e2, true_and, and_true]
  exact ⟨(by simpa only [e5, e13, e7, e11, e10, e15, e8, e2] using (H (7,14) (by decide))), (by simpa only [e5, e13, e7, e11, e10, e15, e8, e2] using (H (0,1) (by decide))), (by simpa only [e5, e13, e7, e11, e10, e15, e8, e2] using (H (14,15) (by decide)))⟩

def witness : List (Fin 3) := [1, 2, 1, 2, 0, 1, 2, 1, 2, 0, 2, 1, 0, 1, 0, 2, 1, 0]

theorem feasible :
    edges.all (fun e => witness[e.1]! != witness[e.2]!) = true := by decide

/-- Every nontrivial proper contiguous slice misses some integer in its range. -/
def intervalTest (p : List Nat) :=
  (List.range p.length).all fun i =>
    (List.range (p.length-i+1)).all fun d =>
      if d < 2 || p.length <= d then true else
        let xs := (p.drop i).take d
        match xs.min?, xs.max? with
        | some a, some b => b-a+1 != d
        | _, _ => false

theorem simple : intervalTest blue = true := by decide

/-- Ordered pairs with the orientation determined by a named palette. -/
def forward (a b d x y : Fin 3) : Prop :=
  (x = a ∧ y = b) ∨ (x = b ∧ y = d) ∨ (x = d ∧ y = a)

private theorem step (a b d x y z : Fin 3)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hxy : forward a b d x y) (hxz : x ≠ z) (hyz : y ≠ z) :
    forward a b d y z := by
  rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact .inr (.inl ⟨rfl, diamond x y z d hab hxz.symm hyz.symm had.symm hbd.symm⟩)
  · exact .inr (.inr ⟨rfl, diamond x y z a hbd hxz.symm hyz.symm hab had⟩)
  · exact .inl ⟨rfl, diamond x y z b had.symm hxz.symm hyz.symm hbd hab.symm⟩

/-- Each consecutive triple in a square path continues the orientation of
its first two colors. The pair indexed by k is reached for every length. -/
theorem rotation_persists (a b d : Fin 3) (x : Nat → Fin 3) (k : Nat)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (start : forward a b d (x 0) (x 1))
    (adjacent : ∀ i, i ≤ k → x i ≠ x (i+1))
    (skip : ∀ i, i < k → x i ≠ x (i+2)) :
    forward a b d (x k) (x (k+1)) := by
  induction k with
  | zero => exact start
  | succ k ih =>
    have prev := ih (fun i hi => adjacent i (by omega)) (fun i hi => skip i (by omega))
    exact step a b d (x k) (x (k+1)) (x (k+2)) hab had hbd prev
      (skip k (by omega)) (adjacent (k+1) (by omega))

/-- Opposite prescribed orientations at the two ends are incompatible. -/
theorem opposite_ends_impossible (a b d : Fin 3) (x : Nat → Fin 3) (k : Nat)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (first : x 0 = a) (second : x 1 = b)
    (penultimate : x k = a) (last : x (k+1) = d)
    (adjacent : ∀ i, i ≤ k → x i ≠ x (i+1))
    (skip : ∀ i, i < k → x i ≠ x (i+2)) : False := by
  have hp := rotation_persists a b d x k hab had hbd (.inl ⟨first,second⟩) adjacent skip
  rw [penultimate,last] at hp
  rcases hp with h | h | h
  · exact hbd h.2.symm
  · exact hab h.1
  · exact had h.1

/-- Insert a square strip of k+2 vertices in the red gap 13→14 and insert
its parity lanes in the blue gaps 8→5 and 15→0 of `blue`. Both possible
parities at the far end give the same contradiction. -/
theorem anchored_strip_impossible (c x : Nat → Fin 3) (k : Nat)
    (anchor : Proper c)
    (adjacent : ∀ i, i ≤ k → x i ≠ x (i+1))
    (skip : ∀ i, i < k → x i ≠ x (i+2))
    (firstRed : x 0 ≠ c 13) (lastRed : x (k+1) ≠ c 14)
    (firstOdd : x 0 ≠ c 8) (firstEven : x 1 ≠ c 15)
    (outerBlue : x (k+1) ≠ c 5 ∨ x (k+1) ≠ c 0)
    (innerBlue : x k ≠ c 5 ∨ x k ≠ c 0) : False := by
  obtain ⟨b5,b0,a15,rb,ra,ba⟩ := forced c anchor
  rw [← a15] at firstEven
  simp only [← b5, ← b0, or_self] at outerBlue innerBlue
  have first := diamond (c 13) (c 8) (x 0) (c 14) ra firstRed firstOdd rb.symm ba
  have last := diamond (c 14) (c 13) (x (k+1)) (c 8) rb.symm lastRed outerBlue ba.symm ra.symm
  have leftEdge := adjacent 0 (by omega)
  have rightEdge := adjacent k (by omega)
  rw [first] at leftEdge
  rw [last] at rightEdge
  have second := diamond (c 14) (c 8) (x 1) (c 13) ba leftEdge.symm firstEven rb ra
  have penultimate := diamond (c 13) (c 8) (x k) (c 14) ra innerBlue rightEdge rb.symm ba
  exact opposite_ends_impossible (c 14) (c 13) (c 8) x k rb.symm ba ra
    first second penultimate last adjacent skip

/-- The tabulated coloring witnesses feasibility of the opened anchor as a proposition. -/
theorem anchor_realized : ∃ c, Proper c ∧ c 13 = 1 ∧ c 14 = 0 ∧ c 8 = 2 := by
  refine ⟨fun i => witness[i]!, ?_, by decide, by decide, by decide⟩
  intro e he
  have h := List.all_eq_true.mp feasible e he
  simpa using h

end OnePointStrip18
