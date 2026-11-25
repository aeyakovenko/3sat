import Std

namespace SparseRankPairCertificate

/-- Four consecutive bits per column, least significant column first. -/
def col (m i : Nat) : Nat := (m >>> (4*i)) % 16

def matVec (m v : Nat) : Nat :=
  (if v.testBit 0 then col m 0 else 0) ^^^
  (if v.testBit 1 then col m 1 else 0) ^^^
  (if v.testBit 2 then col m 2 else 0) ^^^
  (if v.testBit 3 then col m 3 else 0)

def pack (f : Nat → Nat) : Nat := f 0 + 16*f 1 + 256*f 2 + 4096*f 3

def row (m i : Nat) : Nat :=
  (if (col m 0).testBit i then 1 else 0) +
  (if (col m 1).testBit i then 2 else 0) +
  (if (col m 2).testBit i then 4 else 0) +
  (if (col m 3).testBit i then 8 else 0)

def transpose (m : Nat) : Nat := pack (row m)

/-- Multiplication in the polynomial basis modulo X⁴ + X + 1. -/
def timesX (x : Nat) : Nat :=
  if x.testBit 3 then (2*x) ^^^ 19 else 2*x

def multMatrix (a : Nat) : Nat := pack (fun i => Nat.rec a (fun _ x => timesX x) i)

def orbitPoint (m a b : Nat) : Nat :=
  pack (fun i => matVec (multMatrix a) (matVec m (col (multMatrix b) i)))

def reps : List Nat := [0, 1, 0x12e9, 0x12f4, 0x12f5, 0x12fb, 0x1394, 0x139c,
  0x139d, 0x13ad, 0x13b7, 0x13c4, 0x13d5, 0x13db, 0x13e5, 0x13eb, 0x13fa, 0x14d6]

def support : List Nat :=
  (reps.flatMap fun m => (List.range 15).flatMap fun a =>
    (List.range 15).map fun b => orbitPoint m (a+1) (b+1)).eraseDups

def kernelSize (m : Nat) : Nat := (List.range 16).countP (fun v => matVec m v == 0)

/-- The sizes of the vector kernels certify ranks one and four for nonzero atoms. -/
theorem supportFacts : support.length = 3526 ∧ support.Nodup ∧
    support.count 0 = 1 ∧
    (support.all (fun m => m < 65536 && (m == 0 || kernelSize m == 8 || kernelSize m == 1))) = true := by
  native_decide

/-- Indices 0..15 query M, and indices 16..31 query its transpose. -/
def answer (m : Nat) (p : Fin 32) : Nat :=
  matVec (if p.val < 16 then m else transpose m) (p.val % 16)

def packet (m : Nat) : Array Nat := Array.ofFn (fun p : Fin 32 => answer m p)

def packets : List (Array Nat) := support.map packet

def keys (p q : Fin 32) (a : Array Nat) : Nat := 16*a[p.val]! + a[q.val]!

def histogram {α : Type} (key : α → Nat) (s : List α) : Nat :=
  s.foldr (fun x h => (2 ^ key x) ^^^ h) 0

/-- Bit i records odd multiplicity of answer i. No restriction on equal queries. -/
theorem histogramsVanish : ∀ p q : Fin 32, histogram (keys p q) packets = 0 := by
  native_decide

theorem histogramBit {α : Type} (key : α → Nat) (s : List α) (i : Nat) :
    (histogram key s).testBit i = decide (s.countP (fun x => key x == i) % 2 = 1) := by
  induction s with
  | nil => simp [histogram, Nat.zero_testBit]
  | cons x xs ih =>
    change ((2 ^ key x) ^^^ histogram key xs).testBit i = _
    rw [Nat.testBit_xor, Nat.testBit_two_pow, ih, List.countP_cons]
    by_cases h : key x = i
    · simp [h]
      by_cases hpar : xs.countP (fun x => key x == i) % 2 = 1 <;> simp [hpar] <;> omega
    · simp [h]

/-- All possible answer pairs, including prescribed answers to zero and repeated probes. -/
theorem evenPairFibers (p q : Fin 32) (i : Nat) :
    packets.countP (fun a => keys p q a == i) % 2 = 0 := by
  have h := histogramBit (keys p q) packets i
  rw [histogramsVanish] at h
  simp at h
  omega

@[simp] theorem packetEntry (m : Nat) (p : Fin 32) : (packet m)[p.val]! = answer m p := by
  rw [getElem!_pos]
  · simp [packet]
  · simp [packet]

structure Cylinder where
  first : Fin 32
  second : Fin 32
  reply : Nat

def Cylinder.hit (c : Cylinder) (m : Nat) : Bool :=
  16 * answer m c.first + answer m c.second == c.reply

def parity {α : Type} (s : List α) (f : α → Bool) : Bool :=
  s.foldr (fun x h => f x ^^ h) false

private theorem parityCount {α : Type} (s : List α) (f : α → Bool) :
    parity s f = decide (s.countP f % 2 = 1) := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    change (f x ^^ parity xs f) = _
    rw [ih, List.countP_cons]
    cases hx : f x <;> simp
    by_cases h : xs.countP f % 2 = 1 <;> simp [h] <;> omega

theorem cylinderParity (c : Cylinder) : parity support c.hit = false := by
  have h := evenPairFibers c.first c.second c.reply
  simp [packets, keys, Function.comp_def] at h
  change support.countP c.hit % 2 = 0 at h
  rw [parityCount, h]
  decide

private theorem parityAdd {α : Type} (s : List α) (f g : α → Bool) :
    parity s (fun x => f x ^^ g x) = (parity s f ^^ parity s g) := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    change ((f x ^^ g x) ^^ parity xs (fun y => f y ^^ g y)) =
      ((f x ^^ parity xs f) ^^ (g x ^^ parity xs g))
    rw [ih]
    cases f x <;> cases g x <;> cases parity xs f <;> cases parity xs g <;> rfl

private theorem parityExt {α : Type} (s : List α) (f g : α → Bool)
    (h : ∀ x ∈ s, f x = g x) : parity s f = parity s g := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    change (f x ^^ parity xs f) = (g x ^^ parity xs g)
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

def value (terms : List Cylinder) (m : Nat) : Bool :=
  parity terms (fun c => c.hit m)

theorem representationParity (terms : List Cylinder) : parity support (value terms) = false := by
  induction terms with
  | nil =>
    change parity support (fun _ => false) = false
    simp [parityCount]
  | cons c cs ih =>
    change parity support (fun m => c.hit m ^^ value cs m) = false
    rw [parityAdd, cylinderParity, ih]
    rfl

private theorem parityAtZero (s : List Nat) (one : s.count 0 = 1) :
    parity s (fun m => m == 0) = true := by
  rw [parityCount]
  change decide (s.count 0 % 2 = 1) = true
  rw [one]
  rfl

/-- On all matrices of ranks 0, 1, 4, no sum over F₂ of two-probe cylinders equals δ₀. -/
theorem noTwoQueryRepresentation (terms : List Cylinder) :
    ¬ (∀ m, m < 65536 → (m = 0 ∨ kernelSize m = 8 ∨ kernelSize m = 1) →
      value terms m = (m == 0)) := by
  intro alleged
  have hmem : ∀ m ∈ support, value terms m = (m == 0) := by
    intro m hm
    have h := List.all_eq_true.mp supportFacts.2.2.2 m hm
    simp at h
    apply alleged m h.1
    rcases h.2 with (hz | hone) | hfour
    · exact Or.inl hz
    · exact Or.inr (Or.inl hone)
    · exact Or.inr (Or.inr hfour)
  have h := parityExt support (value terms) (fun m => m == 0) hmem
  rw [representationParity, parityAtZero support supportFacts.2.2.1] at h
  contradiction

end SparseRankPairCertificate
