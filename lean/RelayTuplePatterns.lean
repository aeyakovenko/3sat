import Std

namespace RelayTuplePatterns

/-- A claim on coordinates of a labeling. An unspecified coordinate is free. -/
inductive Pattern : Nat → Type where
  | nil : Pattern 0
  | cons {n : Nat} : Option Bool → Pattern n → Pattern (n+1)

inductive Labeling : Nat → Type where
  | nil : Labeling 0
  | cons {n : Nat} : Bool → Labeling n → Labeling (n+1)

def free : Pattern n → Nat
  | .nil => 0
  | .cons none p => free p + 1
  | .cons (some _) p => free p

def hit : Pattern n → Labeling n → Nat
  | .nil, .nil => 1
  | .cons none p, .cons _ v => hit p v
  | .cons (some a) p, .cons b v => if a = b then hit p v else 0

def cubeSum : (n : Nat) → (Labeling n → Nat) → Nat
  | 0, f => f .nil
  | n+1, f => cubeSum n (fun v => f (.cons false v)) +
                 cubeSum n (fun v => f (.cons true v))

private theorem sumZero (n : Nat) : cubeSum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [cubeSum, ih]

private theorem sumAdd (n : Nat) (f g : Labeling n → Nat) :
    cubeSum n (fun v => f v + g v) = cubeSum n f + cubeSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cubeSum, ih]
    omega

theorem completions (p : Pattern n) : cubeSum n (hit p) = 2 ^ free p := by
  induction p with
  | nil => rfl
  | @cons n bit p ih =>
    cases bit with
    | none => simp [cubeSum, hit, free, ih, Nat.pow_succ, Nat.mul_two]
    | some b => cases b <;> simp [cubeSum, hit, free, ih, sumZero]

def score (v : Labeling n) : List (Pattern n) → Nat
  | [] => 0
  | p :: ps => hit p v + score v ps

private theorem totalScore (ps : List (Pattern n)) :
    cubeSum n (fun v => score v ps) = (ps.map (fun p => 2 ^ free p)).sum := by
  induction ps with
  | nil => exact sumZero n
  | cons p ps ih => simp [score, sumAdd, completions, ih]

private theorem aboveAverage (n : Nat) (f : Labeling n → Nat) :
    ∃ v, cubeSum n f ≤ 2^n * f v := by
  induction n with
  | zero => exact ⟨.nil, by simp [cubeSum]⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih (fun v => f (.cons false v))
    obtain ⟨b, hb⟩ := ih (fun v => f (.cons true v))
    by_cases h : f (.cons false a) ≤ f (.cons true b)
    · refine ⟨.cons true b, ?_⟩
      have hh := Nat.mul_le_mul_left (2^n) h
      simp only [cubeSum, Nat.pow_succ, Nat.mul_two, Nat.add_mul]
      omega
    · refine ⟨.cons false a, ?_⟩
      have hh := Nat.mul_le_mul_left (2^n) (Nat.le_of_not_ge h)
      simp only [cubeSum, Nat.pow_succ, Nat.mul_two, Nat.add_mul]
      omega

/-- An arbitrary collection of prescribed patterns on m distinct coordinates
    each admits a single labeling hitting at least a 2^(-m) fraction. -/
theorem sharedLabeling (m w : Nat) (ps : List (Pattern (w+m)))
    (shape : ∀ p ∈ ps, free p = w) :
    ∃ v, ps.length ≤ 2^m * score v ps := by
  have mass : (ps.map (fun p => 2 ^ free p)).sum = 2^w * ps.length := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      have eq := shape p (by simp)
      have rest := ih (fun x hx => shape x (by simp [hx]))
      simp [eq, rest, Nat.mul_add, Nat.add_comm]
  obtain ⟨v, hv⟩ := aboveAverage (w+m) (fun v => score v ps)
  refine ⟨v, ?_⟩
  rw [totalScore, mass, Nat.pow_add, Nat.mul_assoc] at hv
  exact Nat.le_of_mul_le_mul_left hv (Nat.pow_pos (by decide))

end RelayTuplePatterns
