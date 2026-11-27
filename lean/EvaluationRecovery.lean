import Std

namespace EvaluationRecovery

variable {I W V : Type}

private def total {α : Type} (xs : List α) (f : α → Nat) : Nat :=
  (xs.map f).sum

private theorem total_add {α : Type} (xs : List α) (f g : α → Nat) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ← Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at * <;> omega

private theorem total_const_mul {α : Type} (xs : List α) (a : Nat) (f : α → Nat) :
    total xs (fun x => a * f x) = a * total xs f := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    simpa [total, Nat.mul_add] using congrArg (a * f x + ·) ih

private theorem total_mono {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : total xs f ≤ total xs g := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

private theorem total_zero {α : Type} (xs : List α) (f : α → Nat)
    (h : ∀ x ∈ xs, f x = 0) : total xs f = 0 := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    change f x + total xs f = 0
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

private theorem total_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    total xs (fun x => total ys (f x)) = total ys (fun y => total xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    exact (total_zero ys _ (by simp [total])).symm
  | cons x xs ih =>
    change total ys (f x) + total xs (fun z => total ys (f z)) =
      total ys (fun y => f x y + total xs (fun z => f z y))
    rw [total_add, ih]

private theorem count_or_le {α : Type} (xs : List α) (a b : α → Bool) :
    xs.countP (fun x => a x || b x) ≤ xs.countP a + xs.countP b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases h : a x <;> cases k : b x <;> simp [List.countP_cons, h,k] <;> omega

private theorem count_split {α : Type} (xs : List α) (a : α → Bool) :
    xs.countP (fun x => !(a x)) + xs.countP a = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases h : a x <;> simp [List.countP_cons, h] <;> omega

/-- Coordinates are counted with their positions in the input list. Rivals
    need not be distinct. Each agrees on at most d coordinate positions. -/
theorem collisionUnion (coords : List I) (rivals : List W) (clash : W → I → Bool)
    (d : Nat) (pair : ∀ z ∈ rivals, coords.countP (clash z) ≤ d) :
    coords.countP (fun i => rivals.any (fun z => clash z i)) ≤ rivals.length * d := by
  induction rivals with
  | nil => simp
  | cons z zs ih =>
    have hz := pair z (by simp)
    have ht := ih (fun y hy => pair y (by simp [hy]))
    have hu := count_or_le coords (clash z) (fun i => zs.any (fun y => clash y i))
    simpa [List.any_cons, Nat.succ_mul, Nat.add_comm] using
      (Nat.le_trans hu (Nat.add_le_add hz ht))

def privateAt [DecidableEq V] (label : W → I → V) (rivals : List W) (y : W) (i : I) : Bool :=
  !(rivals.any fun z => decide (label z i = label y i))

theorem privateCoordinates [DecidableEq V] (coords : List I) (rivals : List W)
    (label : W → I → V) (y : W) (d : Nat)
    (pair : ∀ z ∈ rivals, coords.countP (fun i => decide (label z i = label y i)) ≤ d) :
    coords.length ≤ coords.countP (privateAt label rivals y) + rivals.length * d := by
  have h := collisionUnion coords rivals (fun z i => decide (label z i = label y i)) d pair
  have hs := count_split coords (fun i => rivals.any (fun z => decide (label z i = label y i)))
  unfold privateAt
  dsimp only at h
  omega

/-- No rival in the list can claim the same field cell. -/
theorem privateSeparates [DecidableEq V] (label : W → I → V) (rivals : List W)
    (y z : W) (i : I) (hz : z ∈ rivals) (hy : privateAt label rivals y i = true) :
    label z i ≠ label y i := by
  intro he
  have hc : rivals.any (fun t => decide (label t i = label y i)) = true :=
    List.any_eq_true.mpr ⟨z,hz, by simp [he]⟩
  simp [privateAt, hc] at hy

private theorem atMostOne (ws : List W) (sel : W → Bool) (f : W → Nat) (cap : Nat)
    (nd : ws.Nodup)
    (bound : ∀ w ∈ ws, sel w = true → f w ≤ cap)
    (unique : ∀ w ∈ ws, ∀ z ∈ ws, sel w = true → sel z = true → w = z) :
    total ws (fun w => if sel w then f w else 0) ≤ cap := by
  induction ws with
  | nil => simp [total]
  | cons w ws ih =>
    obtain ⟨hw, hnd⟩ := List.nodup_cons.mp nd
    change (if sel w then f w else 0) + total ws _ ≤ cap
    cases hs : sel w with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact ih hnd (fun z hz => bound z (by simp [hz]))
        (fun x hx z hz => unique x (by simp [hx]) z (by simp [hz]))
    | true =>
      have hzero : total ws (fun z => if sel z then f z else 0) = 0 := by
        apply total_zero
        intro z hz
        cases hh : sel z with
        | false => rfl
        | true =>
          have eq := unique w (by simp) z (by simp [hz]) hs hh
          exact (hw (eq ▸ hz)).elim
      simpa [hzero] using bound w (by simp) hs

private theorem oneSlot [DecidableEq V] (vs : List V) (v : V) (weight : Nat)
    (present : v ∈ vs) :
    weight ≤ total vs (fun x => if v = x then weight else 0) := by
  induction vs with
  | nil => simp at present
  | cons x xs ih =>
    change weight ≤ (if v = x then weight else 0) + total xs _
    by_cases h : v = x
    · simp [h]
    · have ht := ih ((List.mem_cons.mp present).resolve_left h)
      simpa [h] using ht

private theorem chargedCount (isClaim : I → Bool) (coords : List I) (u : Nat) :
    coords.countP isClaim * u = total coords (fun i => if isClaim i then u else 0) := by
  induction coords with
  | nil => simp [total]
  | cons i coords ih =>
    cases h : isClaim i <;> simp [total, List.countP_cons, h, Nat.succ_mul, Nat.add_comm] at * <;> exact ih

/-- Clear the common denominator of a finite cell measure. A row that owns at
    least half the coordinates charges its score to its own cells. Summing
    scores costs at most twice the total cell mass. -/
theorem privateMassPacking [DecidableEq V] (ws : List W) (coords : List I) (vs : List V)
    (label : W → I → V) (owns : W → I → Bool) (u : W → Nat) (mass : I → V → Nat)
    (nd : ws.Nodup) (inRange : ∀ w ∈ ws, ∀ i ∈ coords, label w i ∈ vs)
    (half : ∀ w ∈ ws, coords.length ≤ 2 * coords.countP (owns w))
    (cell : ∀ w ∈ ws, ∀ i ∈ coords, owns w i = true → u w ≤ mass i (label w i))
    (privateCell : ∀ i ∈ coords, ∀ a ∈ ws, ∀ b ∈ ws,
      owns a i = true → owns b i = true → label a i = label b i → a = b) :
    coords.length * (ws.map u).sum ≤ 2 * (coords.map (fun i => (vs.map (mass i)).sum)).sum := by
  let row := fun w i => if owns w i then u w else 0
  let slot := fun i v w => if (owns w i && decide (label w i = v)) then u w else 0
  have rowle : ∀ i ∈ coords, ∀ w ∈ ws, row w i ≤ total vs (fun v => slot i v w) := by
    intro i hi w hw
    cases hs : owns w i with
    | false => simp [row, hs]
    | true => simpa [row, slot, hs] using oneSlot vs (label w i) (u w) (inRange w hw i hi)
  have slotle : ∀ i ∈ coords, ∀ v, total ws (slot i v) ≤ mass i v := by
    intro i hi v
    apply atMostOne ws (fun w => owns w i && decide (label w i = v)) u (mass i v) nd
    · intro w hw hx
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
      obtain ⟨a, eq⟩ := hx
      exact eq ▸ cell w hw i hi a
    · intro a ha b hb aa bb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at aa bb
      obtain ⟨ax,av⟩ := aa
      obtain ⟨bx,bv⟩ := bb
      exact privateCell i hi a ha b hb ax bx
        (av.trans bv.symm)
  have allCells : total ws (fun w => total coords (row w)) ≤ total coords (fun i => total vs (mass i)) := by
    rw [total_swap]
    apply total_mono
    intro i hi
    calc
      _ ≤ total ws (fun w => total vs (fun v => slot i v w)) :=
        total_mono _ _ _ (rowle i hi)
      _ = total vs (fun v => total ws (slot i v)) := total_swap ws vs _
      _ ≤ total vs (mass i) := total_mono _ _ _ (fun v _ => slotle i hi v)
  change coords.length * total ws u ≤ 2 * total coords (fun i => total vs (mass i))
  calc
    _ = total ws (fun w => coords.length * u w) := (total_const_mul _ _ _).symm
    _ ≤ total ws (fun w => 2 * total coords (row w)) := by
      apply total_mono
      intro w hw
      rw [show total coords (row w) = coords.countP (owns w) * u w from (chargedCount ..).symm]
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (half w hw)
    _ = 2 * total ws (fun w => total coords (row w)) := total_const_mul _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ allCells

/-- Pairwise agreement and the coordinate count alone make the mass
    packing apply, using all other distinct rows as rivals. -/
theorem codedMassPacking [DecidableEq W] [DecidableEq V] (ws : List W) (coords : List I)
    (vs : List V) (label : W → I → V) (u : W → Nat) (mass : I → V → Nat)
    (d : Nat) (nd : ws.Nodup)
    (inRange : ∀ w ∈ ws, ∀ i ∈ coords, label w i ∈ vs)
    (agreement : ∀ y ∈ ws, ∀ z ∈ ws, z ≠ y →
      coords.countP (fun i => decide (label z i = label y i)) ≤ d)
    (enough : 2 * ((ws.length - 1) * d) ≤ coords.length)
    (cell : ∀ w ∈ ws, ∀ i ∈ coords, u w ≤ mass i (label w i)) :
    coords.length * (ws.map u).sum ≤ 2 * (coords.map (fun i => (vs.map (mass i)).sum)).sum := by
  apply privateMassPacking ws coords vs label (fun w => privateAt label (ws.erase w) w) u mass nd inRange
  · intro w hw
    have pp := privateCoordinates coords (ws.erase w) label w d (by
      intro z hz
      obtain ⟨h,hm⟩ := nd.mem_erase_iff.mp hz
      exact agreement w hw z hm h)
    rw [List.length_erase_of_mem hw] at pp
    omega
  · intro w hw i hi _
    exact cell w hw i hi
  · intro i _ a _ b hb ha _ eql
    apply Classical.byContradiction
    intro hn
    have mem : b ∈ ws.erase a := nd.mem_erase_iff.mpr ⟨Ne.symm hn,hb⟩
    exact (privateSeparates label (ws.erase a) a b i mem ha) eql.symm

private theorem minimumTotal (ws : List W) (u : W → Nat) (c : Nat)
    (h : ∀ w ∈ ws, c ≤ u w) : ws.length * c ≤ total ws u := by
  induction ws with
  | nil => simp [total]
  | cons w ws ih =>
    have hh := h w (by simp)
    have ht := ih (fun v hv => h v (by simp [hv]))
    simpa [total, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hh ht

/-- A normalized measure cannot carry more than 2D rows whose scaled scores
    all exceed its total capacity divided by D. Only 2D+1 rows have to be
    separated simultaneously, irrespective of the original number of rows. -/
theorem retainedCount [DecidableEq W] [DecidableEq V] (ws : List W) (coords : List I)
    (vs : List V) (label : W → I → V) (u : W → Nat) (mass : I → V → Nat)
    (d D cap : Nat) (nd : ws.Nodup) (positive : 0 < cap)
    (inRange : ∀ w ∈ ws, ∀ i ∈ coords, label w i ∈ vs)
    (agreement : ∀ y ∈ ws, ∀ z ∈ ws, z ≠ y →
      coords.countP (fun i => decide (label z i = label y i)) ≤ d)
    (enough : 2 * ((2*D) * d) ≤ coords.length)
    (cell : ∀ w ∈ ws, ∀ i ∈ coords, u w ≤ mass i (label w i))
    (normalized : (coords.map (fun i => (vs.map (mass i)).sum)).sum ≤ cap)
    (threshold : ∀ w ∈ ws, cap ≤ D * (coords.length * u w)) : ws.length ≤ 2*D := by
  apply Classical.byContradiction
  intro small
  let sample := ws.take (2*D+1)
  have hn : sample.length = 2*D+1 := by simp [sample]; omega
  have sub : ∀ w ∈ sample, w ∈ ws := fun w hw => List.mem_of_mem_take hw
  have packed := codedMassPacking sample coords vs label u mass d (nd.take)
    (fun w hw => inRange w (sub w hw))
    (fun y hy z hz => agreement y (sub y hy) z (sub z hz))
    (by simpa [hn] using enough) (fun w hw => cell w (sub w hw))
  have lo := minimumTotal sample (fun w => D * (coords.length * u w)) cap
    (fun w hw => threshold w (sub w hw))
  rw [total_const_mul, total_const_mul] at lo
  change coords.length * total sample u ≤ _ at packed
  have bound : sample.length * cap ≤ (2*D)*cap := calc
    _ ≤ D * (coords.length * total sample u) := lo
    _ ≤ D * (2 * cap) := Nat.mul_le_mul_left _ (Nat.le_trans packed (Nat.mul_le_mul_left _ normalized))
    _ = _ := by rw [← Nat.mul_assoc, Nat.mul_comm D 2]
  have := Nat.le_of_mul_le_mul_right bound positive
  omega

end EvaluationRecovery
