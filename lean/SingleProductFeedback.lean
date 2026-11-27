import Std

namespace SingleProductFeedback

variable {Vertex : Type}

/-- A modular B₃ labelling distinguishes unordered triples with multiplicity. -/
def B3 (slot : Vertex → Int) (period : Int) : Prop :=
  ∀ a b c d e f,
    (slot a + slot b + slot c) % period = (slot d + slot e + slot f) % period →
    ([a,b,c] : List Vertex).Perm [d,e,f]

/-- A signal at h passes the tap for edge i → j to this residue. -/
def arrives (slot : Vertex → Int) (period t : Int) (h i j : Vertex) : Prop :=
  (slot h + slot j - slot i) % period = t % period

private theorem sum_congr {x y p : Int} (h : x % p = y % p) (c : Int) :
    (x+c) % p = (y+c) % p :=
  (Int.emod_add_cancel_right c).2 h

theorem double_unique {slot : Vertex → Int} {p : Int} (good : B3 slot p)
    (a b c d : Vertex) (eq : (slot a + slot b) % p = (slot c + slot d) % p) :
    ([a,b] : List Vertex).Perm [c,d] := by
  have added := sum_congr eq (slot a)
  have rearrange (x y z : Int) : x+y+z = z+x+y := by omega
  rw [rearrange (slot a) (slot b) (slot a), rearrange (slot c) (slot d) (slot a)] at added
  exact List.Perm.cons_inv (good a a b a c d added)

/-- At a genuinely scheduled vertex, each arriving source follows its own edge. -/
theorem regular_slot {slot : Vertex → Int} {p : Int} (good : B3 slot p)
    (h i j dest : Vertex) (edge : i ≠ j)
    (arr : arrives slot p (slot dest) h i j) : h = i ∧ j = dest := by
  have eq := sum_congr arr (slot i)
  have left : slot h + slot j - slot i + slot i = slot h + slot j := by omega
  rw [left, Int.add_comm (slot dest) (slot i)] at eq
  have perm := double_unique good h j i dest eq
  have source : i ∈ ([h,j] : List Vertex) := perm.mem_iff.mpr (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at source
  have same : i = h := source.resolve_right edge
  subst h
  have rest : ([j] : List Vertex).Perm [dest] := List.Perm.cons_inv perm
  exact ⟨rfl, by simpa using rest.mem_iff.mp (by simp : j ∈ [j])⟩

/-- Both banks supply a live bit only when each tap carries its own source,
    both taps target the same vertex, and that vertex owns the current residue. -/
theorem crossing {slot : Vertex → Int} {p t : Int} (good : B3 slot p)
    (h h' i j k l : Vertex) (banks : i ≠ k) (leftEdge : i ≠ j) (rightEdge : k ≠ l)
    (left : arrives slot p t h i j) (right : arrives slot p t h' k l) :
    h = i ∧ h' = k ∧ j = l ∧ t % p = slot j % p := by
  have joined := sum_congr (left.trans right.symm) (slot i + slot k)
  have la : slot h + slot j - slot i + (slot i + slot k) = slot h + slot j + slot k := by omega
  have ra : slot h' + slot l - slot k + (slot i + slot k) = slot h' + slot l + slot i := by omega
  rw [la, ra] at joined
  have perm := good h j k h' l i joined
  have mi : i ∈ ([h,j,k] : List Vertex) := perm.mem_iff.mpr (by simp)
  have mk : k ∈ ([h',l,i] : List Vertex) := perm.mem_iff.mp (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mi mk
  have hi : i = h := mi.resolve_right (fun x => x.elim leftEdge banks)
  have hk : k = h' := mk.resolve_right (fun x => x.elim rightEdge (Ne.symm banks))
  subst h
  subst h'
  classical
  have remaining : j = l := by
    have count := List.Perm.countP_eq (fun x => decide (x = j)) perm
    by_cases hl : l = j
    · exact hl.symm
    · simp [List.countP_cons, hl, leftEdge] at count
  refine ⟨rfl, rfl, remaining, ?_⟩
  change (slot i + slot j - slot i) % p = t % p at left
  rw [show slot i + slot j - slot i = slot j by omega] at left
  exact left.symm

/-- If an edge tap has the same delay residue as another non-loop edge, the
    ordered edges coincide. In particular, disjoint sources yield disjoint banks. -/
theorem distinct_delays {slot : Vertex → Int} {p : Int} (good : B3 slot p)
    (i j k l : Vertex) (loopFree : i ≠ j)
    (equalLag : (slot j - slot i) % p = (slot l - slot k) % p) :
    k = i ∧ j = l := by
  have withK := sum_congr equalLag (slot k)
  rw [show slot l - slot k + slot k = slot l by omega,
      show slot j - slot i + slot k = slot k + slot j - slot i by omega] at withK
  exact regular_slot good k i j l loopFree withK

def xorList : List Bool → Bool
  | [] => false
  | a :: as => a ^^ xorList as

theorem true_term {xs : List Bool} (h : xorList xs = true) : true ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons x tail ih =>
    cases x with
    | false => exact List.mem_cons_of_mem _ (ih (by simpa [xorList] using h))
    | true => simp

/-- The two parity banks can both be true only if a pair of individually live
    taps coincides. No independence or positivity of all XOR summands is needed. -/
theorem off_slot {slot : Vertex → Int} {p t : Int} (good : B3 slot p)
    (L R : List Bool) (noDest : ∀ j, t % p ≠ slot j % p)
    (explain : true ∈ L → true ∈ R → ∃ h h' i j k l,
      i ≠ k ∧ i ≠ j ∧ k ≠ l ∧ arrives slot p t h i j ∧ arrives slot p t h' k l) :
    (xorList L && xorList R) = false := by
  cases hl : xorList L <;> cases hr : xorList R <;> try rfl
  obtain ⟨h,h',i,j,k,l,hik,hij,hkl,a,b⟩ := explain (true_term hl) (true_term hr)
  exact False.elim (noDest j (crossing good h h' i j k l hik hij hkl a b).2.2.2)

/-- The product of two parity banks supplies a homogeneous gate basis using
    one live constant. Negation uses two taps in one bank and one in the other. -/
theorem autonomous_basis (x y : Bool) :
    (xorList [x] && xorList [y]) = (x && y) ∧
    (xorList [true, x] && xorList [true]) = !x ∧
    (xorList [x, y] && xorList [true]) = (x ^^ y) ∧
    (xorList [true] && xorList [true]) = true := by
  cases x <;> cases y <;> decide

/-- Two initial one-valued slots can regenerate four live constant slots.
    The second pair of each period is driven immediately by the first. -/
theorem two_seed_clock (prev : Bool) (hp : prev = true) :
    let first := prev && prev
    let second := first && first
    first = true ∧ second = true := by
  subst prev
  decide

/-- A sticky guard at just the first cell survives all rows of the flattened
    radius-one evolution. The two other operands of its update can be arbitrary. -/
theorem wall_at_row {Cell : Type} (wall : Cell) (rule : Cell → Cell → Cell → Cell)
    {w : Nat} (stream : Nat → Cell) (initial : stream 0 = wall)
    (sticky : ∀ a b, rule a wall b = wall)
    (recurrence : ∀ b, w ≤ b → stream b =
      rule (stream (b-(w+1))) (stream (b-w)) (stream (b-(w-1)))) :
    ∀ r, stream (r*w) = wall := by
  intro r
  induction r with
  | zero => simpa using initial
  | succ r ih =>
    rw [Nat.succ_mul, recurrence (r*w+w) (by omega),
      show r*w+w-w = r*w by omega, ih, sticky]

/-- Each full serial row is a genuine simultaneous circular update. At the
    right end the stream samples the current first cell; both first cells are
    the same wall. The left-end update ignores its misplaced left operand. -/
theorem one_wall_serial_row {Cell : Type} (wall : Cell) (rule : Cell → Cell → Cell → Cell)
    {w : Nat} (width : 2 ≤ w) (stream : Nat → Cell) (initial : stream 0 = wall)
    (sticky : ∀ a b, rule a wall b = wall)
    (recurrence : ∀ b, w ≤ b → stream b =
      rule (stream (b-(w+1))) (stream (b-w)) (stream (b-(w-1))))
    (r j : Nat) (inside : j < w) :
    stream ((r+1)*w+j) =
      rule (stream (r*w + (if j = 0 then w-1 else j-1)))
        (stream (r*w+j)) (stream (r*w + (if j+1 = w then 0 else j+1))) := by
  have wallRow := wall_at_row wall rule stream initial sticky recurrence
  by_cases first : j = 0
  · subst j
    simp only [Nat.add_zero, wallRow, sticky]
  · rw [Nat.succ_mul, recurrence _ (by omega),
        show r*w+w+j-(w+1) = r*w+(j-1) by omega,
        show r*w+w+j-w = r*w+j by omega, if_neg first]
    by_cases last : j+1 = w
    · rw [if_pos last, Nat.add_zero,
          show r*w+w+j-(w-1) = (r+1)*w by rw [Nat.succ_mul]; omega,
          wallRow, wallRow]
    · rw [if_neg last, show r*w+w+j-(w-1) = r*w+(j+1) by omega]

/-- Two live predecessors are necessary for each produced one. If the taps
    are disjoint, a singleton negative-time seed cannot produce a first one. -/
theorem singleton_seed_quiesces (stream : Int → Bool)
    (singleton : ∀ i j, i < 0 → j < 0 → stream i = true → stream j = true → i = j)
    (preds : ∀ n : Nat, stream n = true → ∃ a b : Nat, 0 < a ∧ 0 < b ∧ a ≠ b ∧
      stream ((n : Int) - a) = true ∧ stream ((n : Int) - b) = true) :
    ∀ n : Nat, stream n = false := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases e : stream n with
    | false => rfl
    | true =>
      obtain ⟨a,b,ha,hb,ab,va,vb⟩ := preds n e
      have prior (d : Nat) (hd : 0 < d) (one : stream ((n : Int)-d) = true) :
          (n : Int)-d < 0 := by
        by_cases hn : (n : Int)-d < 0
        · exact hn
        · exfalso
          have eq : ((n-d : Nat) : Int) = (n : Int)-d := by omega
          have zero := ih (n-d) (by omega)
          rw [eq, one] at zero
          contradiction
      have eq := singleton _ _ (prior a ha va) (prior b hb vb) va vb
      omega

end SingleProductFeedback
