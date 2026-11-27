import Std

namespace OneHotSatReads

/-- The first true dictionary reply ends the scan. If there was no true
reply, the final sentinel is the sole true reply. -/
def scan : List Bool → List Bool
  | [] => [true]
  | false :: rest => false :: scan rest
  | true :: rest => true :: List.replicate (rest.length + 1) false

theorem scan_length (hits : List Bool) : (scan hits).length = hits.length + 1 := by
  induction hits with
  | nil => rfl
  | cons b rest ih => cases b <;> simp [scan, ih]

@[simp] private theorem noTrue (n : Nat) : (List.replicate n false).count true = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem one_hot (hits : List Bool) : (scan hits).count true = 1 := by
  induction hits with
  | nil => decide
  | cons b rest ih => cases b <;> simp [scan, ih]

def distance : List Bool → List Bool → Nat
  | x::xs, y::ys => (if x = y then 0 else 1) + distance xs ys
  | _, _ => 0

private theorem distanceAppend (a b c d : List Bool) (len : a.length = b.length) :
    distance (a++c) (b++d) = distance a b + distance c d := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [distance]
  | cons x xs ih =>
    cases b with
    | nil => simp at len
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at len
      simp [distance, ih ys len, Nat.add_assoc]

private theorem distanceRep (n : Nat) (x y : Bool) :
    distance (List.replicate n x) (List.replicate n y) = if x = y then 0 else n := by
  induction n with
  | zero => simp [distance]
  | succ n ih => cases x <;> cases y <;> simp [List.replicate_succ, distance, ih, Nat.add_comm]

private theorem scanFalse (n : Nat) :
    scan (List.replicate n false) = List.replicate n false ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, scan, ih]

private theorem moved (n : Nat) :
    distance (List.replicate (n+1) false) (List.replicate n false ++ [true]) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [List.replicate_succ, List.cons_append, distance, if_true, Nat.zero_add] using ih

theorem scanDistance (hits : List Bool) :
    distance (scan hits) (List.replicate hits.length false ++ [true]) =
      if hits.contains true then 2 else 0 := by
  induction hits with
  | nil => rfl
  | cons b rest ih =>
    cases b
    · simpa [scan, List.replicate_succ, distance] using ih
    · have tail := moved rest.length
      rw [List.replicate_succ] at tail
      simp [scan, List.replicate_succ, distance, tail]

def echo (r : Nat) (good : Bool) := List.replicate r good ++ List.replicate r (!good)

theorem echoCount (r : Nat) (good : Bool) : (echo r good).count true = r := by
  cases good <;> simp [echo]

theorem opposite_echo_distance (r : Nat) : distance (echo r false) (echo r true) = 2*r := by
  rw [echo, echo, distanceAppend _ _ _ _ (by simp), distanceRep, distanceRep]
  simp [Nat.two_mul]

def full (hits : List Bool) (r : Nat) := scan hits ++ echo r (!(hits.contains true))

theorem fixedHistogram (hits : List Bool) (r : Nat) :
    (full hits r).count true = r+1 := by simp [full, one_hot, echoCount, Nat.add_comm]

theorem gap (hits : List Bool) (r : Nat) (someHit : hits.contains true = true) :
    2*r ≤ distance (full hits r) (full (List.replicate hits.length false) r) := by
  have hlen : (scan hits).length = (scan (List.replicate hits.length false)).length := by
    simp [scan_length]
  rw [full, full, distanceAppend _ _ _ _ hlen]
  rw [someHit]
  simp [opposite_echo_distance]

theorem exactGap (hits : List Bool) (r : Nat) (someHit : hits.contains true = true) :
    distance (full hits r) (full (List.replicate hits.length false) r) = 2*r+2 := by
  have hlen : (scan hits).length = (scan (List.replicate hits.length false)).length := by
    simp [scan_length]
  rw [full, full, distanceAppend _ _ _ _ hlen, scanFalse, scanDistance, someHit]
  simp [opposite_echo_distance, Nat.add_comm]

end OneHotSatReads
