import Std

/-! A finite obstruction to representing the five-variable formula
    (a ∨ b ∨ c) ∧ (a ∨ b ∨ d) ∧ (a ∨ c ∨ e) across one binary cut. -/

namespace NestedClauseCycle

def verdict (a b c d e : Bool) : Bool :=
  (a || b || c) && (a || b || d) && (a || c || e)

abbrev Row := Fin 4
abbrev Col := Fin 8

/-- Split a five-bit assignment into two row bits and three column bits,
    in increasing variable order on either side. -/
def inputBit (i j var : Fin 5) (row : Row) (col : Col) : Bool :=
  if var = i then row.val.testBit 0
  else if var = j then row.val.testBit 1
  else col.val.testBit (var.val - (if i < var then 1 else 0) - (if j < var then 1 else 0))

def flatten (i j : Fin 5) (row : Row) (col : Col) : Bool :=
  let x := fun var => inputBit i j var row col
  verdict (x 0) (x 1) (x 2) (x 3) (x 4)

def entries (t : Fin 3) (a b c : Row × Col) : Row × Col :=
  if t = 0 then a else if t = 1 then b else c

def fool (i j : Fin 5) (t : Fin 3) : Row × Col :=
  match i.val, j.val with
  | 0, 1 => entries t (0,3) (1,0) (2,1)
  | 0, 2 => entries t (0,5) (1,0) (2,1)
  | 0, 3 => entries t (0,3) (1,0) (2,2)
  | 0, 4 => entries t (0,3) (1,0) (2,1)
  | 1, 4 | 2, 3 => entries t (0,1) (1,2) (3,0)
  | _, _ => entries t (0,1) (1,4) (2,2)

theorem ones : ∀ i j : Fin 5, i < j → ∀ t : Fin 3,
    flatten i j (fool i j t).1 (fool i j t).2 = true := by decide

theorem crosses : ∀ i j : Fin 5, i < j → ∀ t s : Fin 3, t ≠ s →
    ¬ (flatten i j (fool i j t).1 (fool i j s).2 = true ∧
       flatten i j (fool i j s).1 (fool i j t).2 = true) := by decide

/-- An entry of either rectangle is a one of the claimed cover. -/
def covered {R C : Type} (a : R → Bool) (b : C → Bool)
    (d : R → Bool) (e : C → Bool) (x : R) (y : C) : Bool :=
  (a x && b y) || (d x && e y)

theorem repeatedColor (f : Fin 3 → Bool) :
    ∃ i j : Fin 3, i ≠ j ∧ f i = f j := by
  by_cases h : f 0 = f 1
  · exact ⟨0,1, by decide, h⟩
  by_cases h' : f 0 = f 2
  · exact ⟨0,2, by decide, h'⟩
  refine ⟨1,2,by decide, ?_⟩
  cases e0 : f 0 <;> cases e1 : f 1 <;> cases e2 : f 2 <;> simp_all

theorem foolingThree {R C : Type} (f : R → C → Bool) (r : Fin 3 → R) (c : Fin 3 → C)
    (positive : ∀ i, f (r i) (c i) = true)
    (cross : ∀ i j, i ≠ j → ¬ (f (r i) (c j) = true ∧ f (r j) (c i) = true))
    (a : R → Bool) (b : C → Bool) (d : R → Bool) (e : C → Bool) :
    ¬ ∀ x y, f x y = covered a b d e x y := by
  intro cover
  let color := fun i => a (r i) && b (c i)
  obtain ⟨i, j, ij, eq⟩ := repeatedColor color
  apply cross i j ij
  have pi := positive i
  have pj := positive j
  rw [cover] at pi pj ⊢
  rw [cover]
  simp only [covered, Bool.or_eq_true, Bool.and_eq_true] at pi pj ⊢
  by_cases h : color i = true
  · have hj : color j = true := eq ▸ h
    have hi' : a (r i) = true ∧ b (c i) = true := Bool.and_eq_true_iff.mp h
    have hj' : a (r j) = true ∧ b (c j) = true := Bool.and_eq_true_iff.mp hj
    exact ⟨Or.inl ⟨hi'.1,hj'.2⟩, Or.inl ⟨hj'.1,hi'.2⟩⟩
  · have hj : color j ≠ true := eq ▸ h
    have hi' := pi.resolve_left (fun h' => h (Bool.and_eq_true_iff.mpr h'))
    have hj' := pj.resolve_left (fun h' => hj (Bool.and_eq_true_iff.mpr h'))
    exact ⟨Or.inr ⟨hi'.1,hj'.2⟩, Or.inr ⟨hj'.1,hi'.2⟩⟩

theorem no_two_rectangles (i j : Fin 5) (ordered : i < j)
    (a : Row → Bool) (b : Col → Bool) (d : Row → Bool) (e : Col → Bool) :
    ¬ ∀ x y, flatten i j x y = covered a b d e x y := by
  exact foolingThree _ (fun t => (fool i j t).1) (fun t => (fool i j t).2)
    (ones i j ordered) (crosses i j ordered) a b d e

/-- The other five-variable obstruction uses c,d,e as its third clause. -/
def secondFlatten (i j : Fin 5) (row : Row) (col : Col) : Bool :=
  let x := fun var => inputBit i j var row col
  (x 0 || x 1 || x 2) && (x 0 || x 1 || x 3) && (x 2 || x 3 || x 4)

def secondFool (i j : Fin 5) (t : Fin 3) : Row × Col :=
  if i.val ≤ 1 then entries t (0,3) (1,2) (2,1)
  else if i = 2 && j = 3 then entries t (0,5) (1,1) (3,0)
  else entries t (0,5) (1,4) (2,1)

theorem second_ones : ∀ i j : Fin 5, i < j → ¬ (i = 0 ∧ j = 1) → ∀ t : Fin 3,
    secondFlatten i j (secondFool i j t).1 (secondFool i j t).2 = true := by decide

theorem second_crosses : ∀ i j : Fin 5, i < j → ¬ (i = 0 ∧ j = 1) →
    ∀ t s : Fin 3, t ≠ s →
    ¬ (secondFlatten i j (secondFool i j t).1 (secondFool i j s).2 = true ∧
       secondFlatten i j (secondFool i j s).1 (secondFool i j t).2 = true) := by decide

theorem only_one_possible_cherry (i j : Fin 5) (ordered : i < j)
    (a : Row → Bool) (b : Col → Bool) (d : Row → Bool) (e : Col → Bool)
    (cover : ∀ x y, secondFlatten i j x y = covered a b d e x y) : i = 0 ∧ j = 1 := by
  by_cases good : i = 0 ∧ j = 1
  · exact good
  exfalso
  exact foolingThree _ (fun t => (secondFool i j t).1) (fun t => (secondFool i j t).2)
    (second_ones i j ordered good) (second_crosses i j ordered good)
    a b d e cover

/-- Count the equal successive values among the first n transitions of f. -/
def plateaus (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => plateaus f n + (if f (n+1) = f n then 1 else 0)

theorem plateau_identity (f : Nat → Nat)
    (step : ∀ n, f (n+1) = f n ∨ f (n+1) = f n+1) (n : Nat) :
    plateaus f n + f n = n + f 0 := by
  induction n with
  | zero => simp [plateaus]
  | succ n ih =>
    rcases step n with same | increment
    · simp only [plateaus, same, ↓reduceIte]
      omega
    · have ne : f (n+1) ≠ f n := by omega
      unfold plateaus
      rw [if_neg ne, Nat.add_zero, increment]
      omega

/-- For the six-variable successor, a six-bit mask records the row variables.
    Row and column bit strings follow variable order. -/
def below (mask : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => below mask n + (if mask.testBit n then 1 else 0)

def bit6 (mask row col var : Nat) : Bool :=
  if mask.testBit var then row.testBit (below mask var)
  else col.testBit (var - below mask var)

def sixTable (mask row col : Nat) : Bool :=
  let x := bit6 mask row col
  (x 0 || x 1 || x 2) && (x 0 || x 1 || x 3) &&
    (x 2 || x 3 || x 4) && (x 0 || x 4 || x 5)

abbrev Col16 := Fin 16

def threeEntries (t : Fin 3) (a b c : Row × Col16) : Row × Col16 :=
  if t = 0 then a else if t = 1 then b else c

/-- One three-entry fooling set per two-versus-four cut. -/
def sixPairFool (mask : Fin 64) (t : Fin 3) : Row × Col16 :=
  match mask.val with
  | 3 => threeEntries t (0,7) (1,1) (2,4)
  | 5 | 9 => threeEntries t (0,5) (1,2) (2,6)
  | 17 => threeEntries t (0,11) (1,2) (2,1)
  | 33 => threeEntries t (0,9) (1,2) (2,3)
  | 6 | 10 => threeEntries t (0,3) (1,4) (2,1)
  | 18 => threeEntries t (0,3) (1,10) (2,1)
  | 34 => threeEntries t (0,3) (1,8) (2,6)
  | 12 => threeEntries t (0,5) (1,1) (3,4)
  | 20 | 24 => threeEntries t (0,5) (1,1) (2,2)
  | _ => threeEntries t (0,5) (1,1) (2,6)

set_option maxRecDepth 5000 in
theorem six_pair_ones : ∀ m : Fin 64, below m.val 6 = 2 → ∀ t : Fin 3,
    sixTable m.val (sixPairFool m t).1.val (sixPairFool m t).2.val = true := by decide

set_option maxRecDepth 5000 in
theorem six_pair_crosses : ∀ m : Fin 64, below m.val 6 = 2 → ∀ t s : Fin 3, t ≠ s →
    ¬ (sixTable m.val (sixPairFool m t).1.val (sixPairFool m s).2.val = true ∧
       sixTable m.val (sixPairFool m s).1.val (sixPairFool m t).2.val = true) := by decide

theorem six_no_cherry (mask : Fin 64) (two : below mask.val 6 = 2)
    (a : Row → Bool) (b : Col16 → Bool) (d : Row → Bool) (e : Col16 → Bool) :
    ¬ ∀ x : Row, ∀ y : Col16, sixTable mask.val x.val y.val = covered a b d e x y := by
  exact foolingThree (fun (x : Row) (y : Col16) => sixTable mask.val x.val y.val)
    (fun t => (sixPairFool mask t).1) (fun t => (sixPairFool mask t).2)
    (six_pair_ones mask two) (six_pair_crosses mask two) a b d e

def fiveEntries (t : Fin 5) (a b c d e : Col × Col) : Col × Col :=
  if t = 0 then a else if t = 1 then b else if t = 2 then c else if t = 3 then d else e

/-- A triple cut is represented by its side containing variable zero. -/
def needsFive (mask : Fin 64) : Bool :=
  below mask.val 6 == 3 && mask.val.testBit 0 && mask.val != 35 && mask.val != 49

def sixTripleFool (mask : Fin 64) (t : Fin 5) : Col × Col :=
  match mask.val with
  | 7 | 11 => fiveEntries t (1,1) (2,2) (4,3) (5,0) (6,4)
  | 19 => fiveEntries t (0,7) (1,1) (2,5) (4,3) (5,0)
  | 13 => fiveEntries t (0,3) (1,2) (2,5) (3,0) (6,4)
  | 21 | 25 => fiveEntries t (0,7) (1,2) (2,5) (3,0) (4,1)
  | _ => fiveEntries t (0,5) (1,2) (2,6) (3,0) (4,3)

set_option maxRecDepth 5000 in
theorem six_triple_ones : ∀ m : Fin 64, needsFive m = true → ∀ t : Fin 5,
    sixTable m.val (sixTripleFool m t).1.val (sixTripleFool m t).2.val = true := by decide

set_option maxRecDepth 5000 in
theorem six_triple_crosses : ∀ m : Fin 64, needsFive m = true → ∀ t s : Fin 5, t ≠ s →
    ¬ (sixTable m.val (sixTripleFool m t).1.val (sixTripleFool m s).2.val = true ∧
       sixTable m.val (sixTripleFool m s).1.val (sixTripleFool m t).2.val = true) := by decide

theorem repeatedFourColors (f : Fin 5 → Fin 4) :
    ∃ i j : Fin 5, i ≠ j ∧ f i = f j := by
  have allCases : ∀ a b c d e : Fin 4,
      a = b ∨ a = c ∨ a = d ∨ a = e ∨ b = c ∨ b = d ∨ b = e ∨ c = d ∨ c = e ∨ d = e := by decide
  rcases allCases (f 0) (f 1) (f 2) (f 3) (f 4) with h|h|h|h|h|h|h|h|h|h
  · exact ⟨0,1,by decide,h⟩
  · exact ⟨0,2,by decide,h⟩
  · exact ⟨0,3,by decide,h⟩
  · exact ⟨0,4,by decide,h⟩
  · exact ⟨1,2,by decide,h⟩
  · exact ⟨1,3,by decide,h⟩
  · exact ⟨1,4,by decide,h⟩
  · exact ⟨2,3,by decide,h⟩
  · exact ⟨2,4,by decide,h⟩
  · exact ⟨3,4,by decide,h⟩

theorem six_no_four_rectangles (mask : Fin 64) (hard : needsFive mask = true)
    (left right : Fin 4 → Col → Bool) :
    ¬ ∀ x y : Col, sixTable mask.val x.val y.val = true ↔
      ∃ k : Fin 4, left k x = true ∧ right k y = true := by
  intro cover
  let r := fun t => (sixTripleFool mask t).1
  let c := fun t => (sixTripleFool mask t).2
  have hasColor (t : Fin 5) : ∃ k, left k (r t) = true ∧ right k (c t) = true :=
    (cover _ _).mp (six_triple_ones mask hard t)
  let color := fun t => Classical.choose (hasColor t)
  have chosen (t) : left (color t) (r t) = true ∧ right (color t) (c t) = true :=
    Classical.choose_spec (hasColor t)
  obtain ⟨i,j,ne,same⟩ := repeatedFourColors color
  have hi := chosen i
  have hj := chosen j
  rw [← same] at hj
  exact six_triple_crosses mask hard i j ne ⟨(cover _ _).mpr ⟨color i,hi.1,hj.2⟩,
    (cover _ _).mpr ⟨color i,hj.1,hi.2⟩⟩

#print axioms six_no_cherry
#print axioms six_no_four_rectangles

#print axioms only_one_possible_cherry
#print axioms plateau_identity
#print axioms no_two_rectangles

end NestedClauseCycle
