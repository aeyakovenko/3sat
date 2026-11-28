import QuadraticOrSeparation

namespace HistoricalQuadraticContinuation
open QuadraticFixedChain

/-- The previous fixed five-to-six map and its unchanged sixteen inherited rows. -/
def previous : Array Nat :=
  #[60,48,50,34,44,47,6,0,46,52,51,0,10,0,0,0,31,25,51,0,55,0,0,0,21,0,0,0,0,0,0,0]
def originalSix : Array Nat := #[5,15,21,22,25,27,28,31,34,41,42,45,51,52,53,59]
def endpoint : Array Nat := #[21,27,38,42,51,53,59,63,82,85,86,91,92,99,105,106]

def coefficients : Array Nat := (List.range 64).toArray.map fun s =>
  match s with
  | 0 => 7 | 1 => 29 | 2 => 14 | 3 => 6 | 4 => 1 | 8 => 3 | 12 => 5
  | 16 => 46 | 24 => 4 | 32 => 96 | 33 => 43 | 48 => 43 | _ => 0

/-- An equivalent construction. XOR the displayed seven-bit word for each
uncovered source edge into one affine insertion from the classified family. -/
def byEdges (x : Nat) : Nat := Id.run do
  let offsets := #[6,0,5,4,43,43]
  let mut y := QuadraticOrSeparation.affine 54 x
  for j in [:6] do
    if !x.testBit j && !x.testBit ((j+1)%6) then y := y ^^^ offsets[j]!
  return y

theorem two_descriptions : ∀ x : Fin 64, poly coefficients x = byEdges x := by native_decide

theorem globally_quadratic : exactQuadratic coefficients ∧ valid 6 (poly coefficients) := by
  native_decide

theorem historical_images :
    valid 5 (poly previous) ∧ exactQuadratic previous ∧
    ((List.range 16).map (fun x => poly previous (CycleImageQuadratic.polynomial x))).mergeSort =
      originalSix.toList ∧ (originalSix.toList.map (poly coefficients)).mergeSort = endpoint.toList := by
  native_decide

theorem fixed_middle_excludes_five : boundedSearch 6 originalSix 5 = false := by native_decide

theorem endpoint_excludes_six : boundedSearch 7 endpoint 6 = false := by native_decide

/-- The upper checks on all 84 separately valid affine successors combine
with the journal's classification to make quadratic degree necessary here. -/
theorem all_affine_images_fit_six : (List.range 84).all (fun i =>
    boundedSearch 7 (originalSix.map (QuadraticOrSeparation.affine i)) 6) = true := by native_decide

/-- Internal adjacency for a nonempty bit path, written by its first bit and tail. -/
def goodFrom (a : Bool) : List Bool → Bool
  | [] => true
  | b :: rest => (a || b) && goodFrom b rest

def lastFrom (a : Bool) : List Bool → Bool
  | [] => a
  | b :: rest => lastFrom b rest

theorem goodFrom_append (a : Bool) (xs ys : List Bool) :
    goodFrom a (xs ++ ys) = (goodFrom a xs && goodFrom (lastFrom a xs) ys) := by
  induction xs generalizing a with
  | nil => simp [goodFrom, lastFrom]
  | cons b xs ih => simp [goodFrom, lastFrom, ih, Bool.and_assoc]

/-- The first and last bits are relevant precisely when all internal edges are covered. -/
def profile (p : Bool × List Bool) : Option (Bool × Bool) :=
  if goodFrom p.1 p.2 then some (p.1, lastFrom p.1 p.2) else none

def cycle (xs : List Bool) : Bool :=
  match xs with
  | [] => true
  | left :: rest => goodFrom left (rest ++ [left])

def oriented (n cut : Nat) (reverse : Bool) (v : Nat) : Bool × List Bool :=
  let pos := fun j => if reverse then (cut+n-j)%n else (cut+1+j)%n
  (v.testBit (pos 0), (List.range (n-1)).map (fun j => v.testBit (pos (j+1))))

theorem preserving_cut : ∀ u : Fin 64,
    profile (oriented 6 1 false u) = profile (oriented 7 2 true (poly coefficients u)) := by
  native_decide

def compatible (a b : Nat) (reverse : Bool) : Bool := (List.range 64).all (fun u =>
  profile (oriented 6 a false u) == profile (oriented 7 b reverse (poly coefficients u)))

theorem unique_cut :
    (((List.range 6).flatMap (fun a => (List.range 7).flatMap (fun b =>
      [false,true].map (fun r => (a,b,r))))).filter (fun (a,b,r) => compatible a b r)) =
      [(1,2,true)] := by native_decide

def join (p : Bool × List Bool) (exterior : List Bool) : List Bool := p.1 :: (p.2 ++ exterior)

private theorem join_depends_on_profile (p : Bool × List Bool) (exterior : List Bool) :
    cycle (join p exterior) = match profile p with
      | none => false
      | some (left,right) => goodFrom right (exterior ++ [left]) := by
  rcases p with ⟨a,tail⟩
  simp only [cycle, join, List.append_assoc, profile]
  rw [goodFrom_append]
  cases h : goodFrom a tail <;> simp [h]

/-- For arbitrary exterior bits, the actual concatenated cycles have the same verdict. -/
theorem substitute_in_every_cycle (u : Fin 64) (exterior : List Bool) :
    cycle (join (oriented 6 1 false u) exterior) =
      cycle (join (oriented 7 2 true (poly coefficients u)) exterior) := by
  rw [join_depends_on_profile, join_depends_on_profile, preserving_cut]

theorem substitution_injective (u v : Fin 64) (outside other : List Bool)
    (h : (poly coefficients u, outside) = (poly coefficients v, other)) :
    u = v ∧ outside = other := by
  have inj : ∀ x y : Fin 64, poly coefficients x = poly coefficients y → x = y := by native_decide
  exact ⟨inj u v (congrArg Prod.fst h), congrArg Prod.snd h⟩

/-- Apply the local substitution repeatedly at the leftmost six path positions.
The first six output bits form the next state. The seventh bit is emitted. -/
private def pathWord (s : Fin 64) : Nat := Id.run do
  let sourceOrder := #[2,3,4,5,0,1]
  let targetOrder := #[2,1,0,6,5,4,3]
  let mut u := 0
  for i in [:6] do
    if s.val.testBit i then u := u ||| (1 <<< sourceOrder[i]!)
  let v := poly coefficients u
  let mut w := 0
  for i in [:7] do
    if v.testBit targetOrder[i]! then w := w ||| (1 <<< i)
  return w

private def nextState (s : Fin 64) : Fin 64 := ⟨pathWord s % 64, Nat.mod_lt _ (by decide)⟩
private def emitted (s : Fin 64) : Bool := (pathWord s).testBit 6
private def after : Nat → Fin 64 → Fin 64
  | 0, s => s
  | k+1, s => after k (nextState s)

theorem state_period_six : ∀ s : Fin 64, after 21 s = after 15 s := by native_decide
private theorem period_two_start : ∀ s : Fin 64,
    emitted (after 17 s) = emitted (after 15 s) := by native_decide

theorem emitted_period_two (k : Nat) (s : Fin 64) :
    emitted (after (17+k) s) = emitted (after (15+k) s) := by
  induction k generalizing s with
  | zero => exact period_two_start s
  | succ k ih => exact ih (nextState s)

theorem bit_period_start_sharp : emitted (after 16 32) ≠ emitted (after 14 32) := by native_decide

end HistoricalQuadraticContinuation
