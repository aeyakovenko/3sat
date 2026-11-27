import Std

/-! Finite correctness and storage accounting for patching a heavy checkpoint
from the nearest preceding light one. Within each interval the list of native
stores is newest first, so its head is the last chronological store. -/

namespace CoarseSnapshotPatches

def latest [DecidableEq A] (a : A) : List (A × W) → Option W
  | [] => none
  | (b, w) :: rest => if a = b then some w else latest a rest

/-- Apply the stores in chronological order, including stores of zero. -/
def replay [DecidableEq A] : List (A × W) → (A → W) → A → W
  | [], base => base
  | (b, w) :: rest, base => fun a => if a = b then w else replay rest base a

private theorem replayAppend [DecidableEq A] (newer older : List (A × W))
    (base : A → W) :
    replay (newer ++ older) base = replay newer (replay older base) := by
  induction newer with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨b, w⟩ := pair
    funext a
    simp only [List.cons_append, replay, ih]

/-- Keep the most recent value of each written key. A missing key falls back
to the saved description; a present zero is a genuine dictionary answer. -/
def compact [DecidableEq A] : List (A × W) → List (A × W)
  | [] => []
  | (a,w) :: rest => (a,w) :: (compact rest).filter (fun p => !decide (p.1 = a))

private theorem latestFilter [DecidableEq A] (xs : List (A × W)) (a b : A)
    (different : a ≠ b) :
    latest a (xs.filter (fun p => !decide (p.1 = b))) = latest a xs := by
  induction xs with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨c, w⟩ := pair
    by_cases same : c = b
    · subst c
      simp [latest, different, ih]
    · simp [latest, same, ih]

theorem compact_correct [DecidableEq A] (xs : List (A × W)) (a : A) :
    latest a (compact xs) = latest a xs := by
  induction xs with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨b, w⟩ := pair
    by_cases same : a = b
    · simp [latest, compact, same]
    · simp [latest, compact, same, latestFilter _ _ _ same, ih]

theorem compact_unique [DecidableEq A] (xs : List (A × W)) :
    (compact xs).Pairwise (fun p q => p.1 ≠ q.1) := by
  induction xs with
  | nil => exact .nil
  | cons pair rest ih =>
    obtain ⟨a, w⟩ := pair
    apply List.pairwise_cons.mpr
    constructor
    · intro p hp
      have test := (List.mem_filter.mp hp).2
      have neq : p.1 ≠ a := by simpa using test
      exact Ne.symm neq
    · exact List.Pairwise.filter _ ih

theorem compact_length [DecidableEq A] (xs : List (A × W)) :
    (compact xs).length ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons pair rest ih =>
    obtain ⟨a,w⟩ := pair
    simp only [compact, List.length_cons]
    have hf := List.length_filter_le (fun p : A × W => !decide (p.1 = a)) (compact rest)
    omega

private theorem latestReplay [DecidableEq A] (xs : List (A × W))
    (base : A → W) (a : A) : (latest a xs).getD (base a) = replay xs base a := by
  induction xs with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨b, w⟩ := pair
    by_cases same : a = b <;> simp [latest, replay, same, ih]

/-- Time zero has a free genuine initial description. The positive cut
indices are those counted by sumRows and heavyCount. -/
def baseIndex (size : Nat → Nat) (v : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => if size (i+1) ≤ v then i+1 else baseIndex size v i

def heavyCount (size : Nat → Nat) (v : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => if size (i+1) ≤ v then heavyCount size v i else heavyCount size v i + 1

def sumRows (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i+1 => sumRows f i + f (i+1)

def history (size : Nat → Nat) (v : Nat) (writes : Nat → List (A × W)) :
    Nat → List (A × W)
  | 0 => []
  | i+1 => if size (i+1) ≤ v then [] else writes i ++ history size v writes i

def actual [DecidableEq A] (writes : Nat → List (A × W)) (initial : A → W) :
    Nat → A → W
  | 0 => initial
  | i+1 => replay (writes i) (actual writes initial i)

theorem base_small (size : Nat → Nat) (v i : Nat) (initialSize : size 0 = 0) :
    size (baseIndex size v i) ≤ v := by
  induction i with
  | zero => simp [baseIndex, initialSize]
  | succ i ih =>
    simp only [baseIndex]
    split <;> assumption

private theorem fromBase [DecidableEq A] (size : Nat → Nat) (v : Nat)
    (writes : Nat → List (A × W)) (initial : A → W) (i : Nat) :
    replay (history size v writes i) (actual writes initial (baseIndex size v i)) =
      actual writes initial i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    by_cases small : size (i+1) ≤ v
    · simp [history, baseIndex, small, replay]
    · simp only [history, baseIndex, if_neg small, replayAppend, ih, actual]

/-- A correct decoder is needed only for the nearest light base (or initial
memory). It need never decode the heavy checkpoint itself. -/
theorem patched_lookup [DecidableEq A] (size : Nat → Nat) (v : Nat)
    (writes : Nat → List (A × W)) (initial decodedBase : A → W) (i : Nat)
    (correctBase : decodedBase = actual writes initial (baseIndex size v i)) (a : A) :
    (latest a (compact (history size v writes i))).getD (decodedBase a) =
      actual writes initial i a := by
  rw [compact_correct, latestReplay, correctBase, fromBase]

theorem heavy_mass (size : Nat → Nat) (v n : Nat) :
    heavyCount size v n * (v + 1) ≤ sumRows size n := by
  induction n with
  | zero => simp [heavyCount, sumRows]
  | succ n ih =>
    by_cases small : size (n+1) ≤ v
    · simp only [heavyCount, if_pos small, sumRows]
      omega
    · simp only [heavyCount, if_neg small, Nat.succ_mul, sumRows]
      omega

theorem history_length (size : Nat → Nat) (v g : Nat) (writes : Nat → List (A × W))
    (cap : ∀ i, (writes i).length ≤ g) (n : Nat) :
    (history size v writes n).length ≤ heavyCount size v n * g := by
  induction n with
  | zero => simp [history, heavyCount]
  | succ n ih =>
    by_cases small : size (n+1) ≤ v
    · simp [history, heavyCount, small]
    · have hc := cap n
      simp only [history, heavyCount, if_neg small, List.length_append, Nat.succ_mul]
      omega

/-- Budget per stored address/value pair, plus one header per checkpoint.
A concrete static dictionary may absorb constant factors into 'entry'. -/
def rowBits [DecidableEq A] (size : Nat → Nat) (v entry header : Nat)
    (writes : Nat → List (A × W)) (i : Nat) : Nat :=
  size (baseIndex size v i) + entry * (compact (history size v writes i)).length + header

theorem row_bound [DecidableEq A] (size : Nat → Nat) (v g entry header i r : Nat)
    (writes : Nat → List (A × W)) (initialSize : size 0 = 0)
    (cap : ∀ j, (writes j).length ≤ g) (count : heavyCount size v i ≤ r) :
    rowBits size v entry header writes i ≤ v + entry * (r*g) + header := by
  have hb := base_small size v i initialSize
  have hl := Nat.le_trans (compact_length _) (history_length size v g writes cap i)
  have hc := Nat.mul_le_mul_left entry (Nat.le_trans hl (Nat.mul_le_mul_right g count))
  unfold rowBits
  omega

/-- With r heavy rows, the copies of light payloads cost at most r*v;
the additional entries cost at most r * entry * (r*g). The original
total and the n headers are charged just once. -/
theorem total_bound [DecidableEq A] (size : Nat → Nat) (v g entry header : Nat)
    (writes : Nat → List (A × W)) (initialSize : size 0 = 0)
    (cap : ∀ i, (writes i).length ≤ g) (n r : Nat) (count : heavyCount size v n ≤ r) :
    sumRows (rowBits size v entry header writes) n ≤
      sumRows size n + heavyCount size v n * (v + entry * (r*g)) + n * header := by
  induction n with
  | zero => simp [sumRows, heavyCount]
  | succ n ih =>
    by_cases small : size (n+1) ≤ v
    · have prev : heavyCount size v n ≤ r := by simpa [heavyCount, small] using count
      have bound := ih prev
      have light : rowBits size v entry header writes (n+1) = size (n+1) + header := by
        simp [rowBits, baseIndex, history, compact, small]
      simp only [sumRows, heavyCount, if_pos small, Nat.succ_mul, light]
      omega
    · have nextCount : heavyCount size v n + 1 ≤ r := by
        simpa [heavyCount, small] using count
      have bound := ih (by omega)
      have next := row_bound size v g entry header (n+1) r writes initialSize cap count
      simp only [sumRows, heavyCount, if_neg small, Nat.succ_mul]
      omega

private theorem heavy_mono (size : Nat → Nat) (v i n : Nat) (le : i ≤ n) :
    heavyCount size v i ≤ heavyCount size v n := by
  induction n with
  | zero =>
    have eq : i = 0 := by omega
    simp [eq]
  | succ n ih =>
    by_cases hi : i ≤ n
    · have prev := ih hi
      by_cases small : size (n+1) ≤ v <;> simp only [heavyCount, small, ↓reduceIte] <;> omega
    · have eq : i = n+1 := by omega
      simp [eq]

/-- Both bounds on one whole grid, with the actual number of heavy rows. -/
theorem grid_budget [DecidableEq A] (size : Nat → Nat) (v g entry header n : Nat)
    (writes : Nat → List (A × W)) (initialSize : size 0 = 0)
    (cap : ∀ i, (writes i).length ≤ g) :
    let r := heavyCount size v n
    let bits := rowBits size v entry header writes
    (∀ i, i ≤ n → bits i ≤ v + entry * (r*g) + header) ∧
    sumRows bits n ≤ sumRows size n + r * (v + entry * (r*g)) + n * header := by
  dsimp only
  constructor
  · intro i hi
    exact row_bound size v g entry header i _ writes initialSize cap (heavy_mono size v i n hi)
  · exact total_bound size v g entry header writes initialSize cap n _ (Nat.le_refl _)

end CoarseSnapshotPatches
