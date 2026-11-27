import Std

namespace AffineProbeReplay

/-- A finite adaptive algorithm can choose the entire next computation from
    the result of the current membership probe. -/
inductive Procedure (X Out : Type) where
  | stop (result : Out)
  | ask (point : X) (next : Bool → Procedure X Out)

abbrev Report (X Out : Type) := List (X × Bool) × Out

private def prepend (x : X) (b : Bool) (report : Report X Out) : Report X Out :=
  ((x,b) :: report.1, report.2)

def truthful (membership : X → Bool) : Procedure X Out → Report X Out
  | .stop result => ([],result)
  | .ask x next => prepend x (membership x) (truthful membership (next (membership x)))

/-- Sparse encoding by zero-based chronological indices of positive replies. -/
def positiveIndices (start : Nat) : List (X × Bool) → List Nat
  | [] => []
  | (_,true) :: tail => start :: positiveIndices (start+1) tail
  | (_,false) :: tail => positiveIndices (start+1) tail

theorem indexLowerBound (start j : Nat) (log : List (X × Bool))
    (hj : j ∈ positiveIndices start log) : start ≤ j := by
  induction log generalizing start with
  | nil => simp [positiveIndices] at hj
  | cons e es ih =>
    obtain ⟨x,b⟩ := e
    cases b with
    | false => have h := ih (start+1) hj; omega
    | true =>
      rcases List.mem_cons.mp hj with same | later
      · omega
      · have h := ih (start+1) later; omega

theorem indexCount (start : Nat) (log : List (X × Bool)) :
    (positiveIndices start log).length = log.countP Prod.snd := by
  induction log generalizing start with
  | nil => simp [positiveIndices]
  | cons e es ih =>
    obtain ⟨x,b⟩ := e
    cases b <;> simp [positiveIndices, List.countP_cons, ih]

/-- Cache hits cost no fresh index. If the probed point keys are all
    distinct, the number of positive positions is bounded by the cardinality
    of any list containing every easy point that was encountered. -/
theorem cachedPositiveBound [DecidableEq X] (log : List (X × Bool)) (start : Nat) (easySet : List X)
    (fresh : (log.map Prod.fst).Nodup)
    (allowed : ∀ entry ∈ log, entry.2 = true → entry.1 ∈ easySet) :
    (positiveIndices start log).length ≤ easySet.length := by
  induction log generalizing start easySet with
  | nil => simp [positiveIndices]
  | cons entry es ih =>
    obtain ⟨x,b⟩ := entry
    obtain ⟨absent, nd⟩ := List.nodup_cons.mp fresh
    cases b with
    | false =>
      exact ih (start+1) easySet nd (fun e he => allowed e (by simp [he]))
    | true =>
      have hx := allowed (x,true) (by simp) rfl
      have tail := ih (start+1) (easySet.erase x) nd (by
        intro e he ht
        have hne : e.1 ≠ x := by
          intro eq
          apply absent
          exact List.mem_map.mpr ⟨e,he,eq⟩
        exact (List.mem_erase_of_ne hne).mpr (allowed e (by simp [he]) ht))
      rw [List.length_erase_of_mem hx] at tail
      have nonempty := List.length_pos_of_mem hx
      simp only [positiveIndices, List.length_cons]
      omega

def nextReply (start : Nat) : List Nat → Bool × List Nat
  | [] => (false,[])
  | head :: tail => if head = start then (true,tail) else (false,head :: tail)

private theorem stepExact (start : Nat) (x : X) (b : Bool) (log : List (X × Bool)) :
    nextReply start (positiveIndices start ((x,b)::log)) = (b,positiveIndices (start+1) log) := by
  cases b with
  | true => simp [positiveIndices, nextReply]
  | false =>
    simp only [positiveIndices]
    cases h : positiveIndices (start+1) log with
    | nil => rfl
    | cons j js =>
      have bound := indexLowerBound (start+1) j log (by simp [h])
      have ne : j ≠ start := by omega
      simp [nextReply, ne]

def replay : Procedure X Out → Nat → List Nat → Report X Out
  | .stop result, _, _ => ([],result)
  | .ask x next, start, indices =>
    let choice := nextReply start indices
    prepend x choice.1 (replay (next choice.1) (start+1) choice.2)

/-- The decoder uses only the positive probe numbers. The reconstructed
    report includes each actual point, its answer, and the terminal output. -/
theorem exactReplay (p : Procedure X Out) (membership : X → Bool) (start : Nat) :
    replay p start (positiveIndices start (truthful membership p).1) = truthful membership p := by
  induction p generalizing start with
  | stop result => rfl
  | ask x next ih =>
    change prepend x _ _ = prepend x (membership x) (truthful membership (next (membership x)))
    simp only [truthful, prepend, replay, stepExact]
    rw [ih (membership x) (start+1)]

/-- Stop after seeing budget many negative (hard) points. All other members
    of the bucket can be skipped once the answer is known. -/
def tested (easy : X → Bool) : Nat → List X → List X
  | 0, _ => []
  | _+1, [] => []
  | k+1, x::xs => x :: (if easy x then tested easy (k+1) xs else tested easy k xs)
termination_by _ bucket => bucket.length

/-- Exactly the first budget negatives of the whole bucket are inspected. -/
theorem testedNegatives (easy : X → Bool) (bucket : List X) (budget : Nat) :
    (tested easy budget bucket).filter (fun x => !(easy x)) =
      (bucket.filter (fun x => !(easy x))).take budget := by
  induction bucket generalizing budget with
  | nil => cases budget <;> simp [tested]
  | cons x xs ih =>
    cases budget with
    | zero => simp [tested]
    | succ k =>
      cases h : easy x <;> simp [tested, h, ih]

def sole : List X → Option X
  | [x] => some x
  | _ => none

private theorem soleFirstTwo (xs : List X) : sole (xs.take 2) = sole xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys => rfl

/-- For a list of distinct points, this returns its unique hard point,
    with none for both zero and at least two. A bucket with repeated
    presentations can be deduplicated before invoking the scan. -/
theorem soleAnswer (easy : X → Bool) (bucket : List X) :
    sole ((tested easy 2 bucket).filter (fun x => !(easy x))) =
      sole (bucket.filter (fun x => !(easy x))) := by
  rw [testedNegatives, soleFirstTwo]

theorem twoNegatives (easy : X → Bool) (bucket : List X) :
    ((tested easy 2 bucket).filter (fun x => !(easy x))).length ≤ 2 := by
  rw [testedNegatives, List.length_take]
  omega

/-- Removing already-cached hard replies cannot increase the number of
    fresh negative probes. 'cached' may have been filled by earlier buckets. -/
theorem twoFreshNegatives (easy cached : X → Bool) (bucket : List X) :
    (((tested easy 2 bucket).filter (fun x => !(easy x))).filter (fun x => !(cached x))).length ≤ 2 :=
  Nat.le_trans (List.length_filter_le ..) (twoNegatives easy bucket)

/-- The list can be the realized buckets of an adaptive search. Repeated
    cells or buckets in different calls do not affect the two-per-call bound. -/
theorem allNegatives (easy : X → Bool) (buckets : List (List X)) :
    (buckets.flatMap (fun b => (tested easy 2 b).filter (fun x => !(easy x)))).length ≤
      2 * buckets.length := by
  induction buckets with
  | nil => simp
  | cons b bs ih =>
    have hh := twoNegatives easy b
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    omega

end AffineProbeReplay
