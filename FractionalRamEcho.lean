import Std

/-! A sharp integer separator for the false CPU logs of the one-address
    repeat-read program. Lists store the latest step first. -/
namespace FractionalRamEcho

private def val (b : Bool) : Int := if b then 1 else 0

structure Row where
  oldWrite : Bool
  first : Bool
  second : Bool

def score : List Row → Int
  | [] => 0
  | r :: rs => 2 * score rs + val r.first + val r.second - 2 * val r.oldWrite

def finalBit : List (Bool × Bool) → Bool
  | [] => false
  | p :: _ => p.1 || p.2

def cpuRows : List (Bool × Bool) → List Row
  | [] => []
  | p :: ps => ⟨finalBit ps, p.1, p.2⟩ :: cpuRows ps

def bonus : List (Bool × Bool) → Nat
  | [] => 0
  | p :: ps => 2 * bonus ps + (p.1 && p.2).toNat

theorem chronological_score (ps : List (Bool × Bool)) :
    score (cpuRows ps) = val (finalBit ps) + (bonus ps : Int) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a,b⟩
    cases a <;> cases b <;>
      simp [cpuRows, finalBit, score, bonus, ih, val, Int.ofNat_add, Int.ofNat_mul] <;> omega

theorem memory_score (ws : List Bool) :
    score (ws.map (fun b => ⟨b,b,b⟩)) = 0 := by
  induction ws with
  | nil => rfl
  | cons b bs ih => simp [score, ih]; omega

/-- Every possible binary bonus is realized while the final OR is one. -/
def reads : Nat → Nat → List (Bool × Bool)
  | 0, _ => []
  | n+1, v => (true, decide (v % 2 = 1)) :: reads n (v/2)

theorem reads_length (n v : Nat) : (reads n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [reads, ih]

theorem bonus_reads (n v : Nat) (h : v < 2^n) : bonus (reads n v) = v := by
  induction n generalizing v with
  | zero => simp [reads, bonus]; omega
  | succ n ih =>
    have hn : v/2 < 2^n := by rw [Nat.pow_succ] at h; omega
    by_cases hh : v % 2 = 1 <;> simp [reads, bonus, ih _ hn, hh] <;> omega

theorem all_false_scores (n v : Nat) (h : v < 2^(n+1)) :
    finalBit (reads (n+1) v) = true ∧ score (cpuRows (reads (n+1) v)) = 1 + (v : Int) := by
  constructor
  · rfl
  · rw [chronological_score, bonus_reads _ _ h]; rfl

/-- Scaled marginals: deviations of all three event frequencies from the
memory-valid frequencies imply a one-step bound for the false CPU population. -/
theorem marginal_step (old next a b memory ew ea eb : Nat)
    (hor : next ≤ a + b) (hw : memory ≤ old + ew)
    (ha : a ≤ memory + ea) (hb : b ≤ memory + eb) :
    next ≤ 2 * (old + (ew + ea + eb)) := by omega

def sumUntil (e : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k+1 => sumUntil e k + e k

theorem accumulated_error (count error : Nat → Nat) (start : count 0 = 0)
    (step : ∀ i, count (i+1) ≤ 2 * (count i + error i)) (n : Nat) :
    count n ≤ 2^n * sumUntil error n := by
  induction n with
  | zero => simp [start, sumUntil]
  | succ n ih =>
    have he : error n ≤ 2^n * error n := by
      have hn := Nat.two_pow_pos n
      simpa using (Nat.mul_le_mul_right (error n) (show 1 ≤ 2^n by omega))
    have ht := step n
    simp only [sumUntil, Nat.pow_succ, Nat.mul_add]
    have hrewrite : 2^n * 2 = 2 * 2^n := Nat.mul_comm _ _
    rw [hrewrite, Nat.mul_assoc, Nat.mul_assoc]
    omega

/-- Folding subsequent per-slot deviations preserves the side of the genuine
score fixed at its earliest differing slot. -/
def laterScore (z : Int) (ds : List Int) : Int :=
  ds.foldl (fun a d => 4 * a + d) z

theorem positive_first (ds : List Int) (z : Int) (hz : 1 ≤ z)
    (tailBound : ∀ d ∈ ds, -2 ≤ d) : 1 ≤ laterScore z ds := by
  induction ds generalizing z with
  | nil => exact hz
  | cons d ds ih =>
    have hd := tailBound d (List.mem_cons_self ..)
    exact ih (4 * z + d) (by omega) (fun t ht => tailBound t (List.mem_cons_of_mem _ ht))

theorem negative_first (ds : List Int) (z : Int) (hz : z ≤ -1)
    (tailBound : ∀ d ∈ ds, d ≤ 1) : laterScore z ds ≤ -1 := by
  induction ds generalizing z with
  | nil => exact hz
  | cons d ds ih =>
    have hd := tailBound d (List.mem_cons_self ..)
    exact ih (4 * z + d) (by omega) (fun t ht => tailBound t (List.mem_cons_of_mem _ ht))

#print axioms positive_first
#print axioms negative_first
#print axioms chronological_score
#print axioms all_false_scores
#print axioms accumulated_error

end FractionalRamEcho
