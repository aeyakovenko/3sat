import Std

namespace XorPathCounts

private theorem cancelLeft (x y : Nat) : x ^^^ (x ^^^ y) = y := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

private theorem cancelRight (x y : Nat) : (x ^^^ y) ^^^ y = x := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

def colorsTwo (x y v : Nat) : Nat × Nat := (x ^^^ v, v ^^^ y)

def colorsThree (x y : Nat) (middle : Nat × Nat) : Nat × Nat × Nat :=
  (x ^^^ middle.1, middle.1 ^^^ middle.2, middle.2 ^^^ y)

theorem twoEndpointSum (x y v : Nat) :
    (colorsTwo x y v).1 ^^^ (colorsTwo x y v).2 = x ^^^ y := by
  simp only [colorsTwo, Nat.xor_assoc, cancelLeft]

theorem threeEndpointSum (x y : Nat) (m : Nat × Nat) :
    (colorsThree x y m).1 ^^^ ((colorsThree x y m).2.1 ^^^ (colorsThree x y m).2.2) =
      x ^^^ y := by
  simp only [colorsThree, Nat.xor_assoc, cancelLeft]

theorem twoColorsInjective (x y v w : Nat) (h : colorsTwo x y v = colorsTwo x y w) :
    v = w := by
  simpa only [colorsTwo, cancelLeft] using congrArg (fun a => x ^^^ a.1) h

theorem threeColorsInjective (x y : Nat) (v w : Nat × Nat)
    (h : colorsThree x y v = colorsThree x y w) : v = w := by
  apply Prod.ext
  · simpa only [colorsThree, cancelLeft] using congrArg (fun a => x ^^^ a.1) h
  · simpa only [colorsThree, cancelRight] using congrArg (fun a => a.2.2 ^^^ y) h

private def pairs (as : List α) (bs : List β) : List (α × β) :=
  as.flatMap (fun a => bs.map (fun b => (a,b)))

private theorem memPairs (as : List α) (bs : List β) (a : α) (b : β) :
    (a,b) ∈ pairs as bs ↔ a ∈ as ∧ b ∈ bs := by simp [pairs]

private theorem lengthPairs (as : List α) (bs : List β) :
    (pairs as bs).length = as.length * bs.length := by
  induction as with
  | nil => simp [pairs]
  | cons a as ih =>
    simp only [pairs, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, Nat.succ_mul] at *
    omega

private theorem capacity {α : Type} [DecidableEq α] (codes pool : List α)
    (nd : codes.Nodup) (inside : ∀ x ∈ codes, x ∈ pool) : codes.length ≤ pool.length := by
  induction codes generalizing pool with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp nd
    have mem := inside x (by simp)
    have pos := List.length_pos_of_mem mem
    have rest := ih (pool.erase x) tail (by
      intro a ha
      have ne : a ≠ x := fun h => fresh (h ▸ ha)
      exact (List.mem_erase_of_ne ne).2 (inside a (by simp [ha])))
    rw [List.length_erase_of_mem mem] at rest
    simp; omega

/-- For fixed endpoint sum z, inject the distinct paths into the palette.
    Decoding z from a color tuple keeps different endpoint sums disjoint. -/
private theorem pathCapacity {P C : Type} [DecidableEq C] (sums : List Nat)
    (paths : Nat → List P) (encode : Nat → P → C) (decode : C → Nat)
    (pool : List C) (k : Nat) (nd : sums.Nodup)
    (localNd : ∀ z ∈ sums, (paths z).Nodup)
    (enough : ∀ z ∈ sums, k ≤ (paths z).length)
    (inj : ∀ z a b, encode z a = encode z b → a = b)
    (recovers : ∀ z a, decode (encode z a) = z)
    (inside : ∀ z ∈ sums, ∀ a ∈ paths z, encode z a ∈ pool) :
    sums.length * k ≤ pool.length := by
  let codes (z : Nat) := (paths z).map (encode z)
  have distinct : (sums.flatMap codes).Nodup := by
    apply List.pairwise_flatMap.2
    constructor
    · intro z hz
      apply List.pairwise_map.2
      exact (localNd z hz).imp (fun h he => h (inj z _ _ he))
    · apply nd.imp
      intro i j ne a ha b hb eq
      obtain ⟨p,_,rfl⟩ := List.mem_map.1 ha
      obtain ⟨p',_,rfl⟩ := List.mem_map.1 hb
      exact ne (by simpa only [recovers] using congrArg decode eq)
  have bound := capacity (sums.flatMap codes) pool distinct (by
    intro c hc
    obtain ⟨z,hz,hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨p,hp,rfl⟩ := List.mem_map.1 hc
    exact inside z hz p hp)
  apply Nat.le_trans _ bound
  clear bound distinct nd localNd inside
  induction sums with
  | nil => simp
  | cons z zs ih =>
    have head := enough z (by simp)
    have tail := ih (fun t ht => enough t (by simp [ht]))
    simp only [List.length_cons, Nat.succ_mul, List.flatMap_cons, List.length_append,
      codes, List.length_map] at *
    omega

/-- k common intermediate vertices for each of L distinct endpoint sums
    yield L*k ≤ B² when both edge colors lie in a palette of size B. -/
theorem twoPathCapacity (sums colors : List Nat) (left : Nat → Nat)
    (middle : Nat → List Nat) (k : Nat) (nd : sums.Nodup)
    (localNd : ∀ z ∈ sums, (middle z).Nodup)
    (enough : ∀ z ∈ sums, k ≤ (middle z).length)
    (edges : ∀ z ∈ sums, ∀ v ∈ middle z,
      left z ^^^ v ∈ colors ∧ v ^^^ (left z ^^^ z) ∈ colors) :
    sums.length * k ≤ colors.length^2 := by
  let encode z := colorsTwo (left z) (left z ^^^ z)
  have bound := pathCapacity sums middle encode (fun t => t.1 ^^^ t.2)
    (pairs colors colors) k nd localNd enough (fun z => twoColorsInjective _ _)
    (fun z v => (twoEndpointSum _ _ v).trans (cancelLeft _ _))
    (fun z hz v hv => (memPairs ..).2 (edges z hz v hv))
  simpa [lengthPairs, Nat.pow_succ] using bound

/-- k paths of length three for each of L distinct endpoint sums yield
    L*k ≤ B³ when all three edge colors lie in a palette of size B. -/
theorem threePathCapacity (sums colors : List Nat) (left : Nat → Nat)
    (middle : Nat → List (Nat × Nat)) (k : Nat) (nd : sums.Nodup)
    (localNd : ∀ z ∈ sums, (middle z).Nodup)
    (enough : ∀ z ∈ sums, k ≤ (middle z).length)
    (edges : ∀ z ∈ sums, ∀ v ∈ middle z,
      left z ^^^ v.1 ∈ colors ∧ v.1 ^^^ v.2 ∈ colors ∧ v.2 ^^^ (left z ^^^ z) ∈ colors) :
    sums.length * k ≤ colors.length^3 := by
  let encode z := colorsThree (left z) (left z ^^^ z)
  have bound := pathCapacity sums middle encode (fun t => t.1 ^^^ (t.2.1 ^^^ t.2.2))
    (pairs colors (pairs colors colors)) k nd localNd enough
    (fun z => threeColorsInjective _ _)
    (fun z v => (threeEndpointSum _ _ v).trans (cancelLeft _ _)) (by
      intro z hz v hv
      obtain ⟨a,b,c⟩ := edges z hz v hv
      exact (memPairs ..).2 ⟨a,(memPairs ..).2 ⟨b,c⟩⟩)
  simpa [lengthPairs, Nat.pow_succ, Nat.mul_assoc] using bound

end XorPathCounts
