import Std

/-! Adaptive membership queries, with an arbitrary separate certificate.
The only oracle promises used are rejection on the empty set, acceptance on
singletons, and uniqueness of the accepting certificate on pairs. -/
namespace TwoWitnessIsolation

inductive Queries (ι : Type) where
  | halt (answer : Bool)
  | ask (index : ι) (onFalse onTrue : Queries ι)

def run (oracle : ι → Bool) : Queries ι → List ι × Bool
  | .halt b => ([], b)
  | .ask i a b =>
    let rest := if oracle i then run oracle b else run oracle a
    (i :: rest.1, rest.2)

/-- The transcript and answer survive any changes away from the queried indices. -/
theorem replay (a b : ι → Bool) (t : Queries ι)
    (h : ∀ u ∈ (run a t).1, a u = b u) : run a t = run b t := by
  induction t with
  | halt => simp [run]
  | ask i l r left right =>
    have same := h i (by simp [run])
    cases hi : a i <;> simp [run, hi, ← same] at h ⊢
    · have e := left (fun u hu => h u hu)
      simp [e]
    · have e := right (fun u hu => h u hu)
      simp [e]

section
variable {ι κ : Type} [DecidableEq ι]
def single (i : ι) (u : ι) := decide (u = i)
def pair (i j : ι) (u : ι) := decide (u = i ∨ u = j)

variable (verifier : κ → Queries ι) (cert : ι → κ)
def transcript (i : ι) := (run (single i) (verifier (cert i))).1

theorem queries_own_index
    (empty : ∀ c, (run (fun _ => false) (verifier c)).2 = false)
    (accept : ∀ i, (run (single i) (verifier (cert i))).2 = true) (i : ι) :
    i ∈ transcript verifier cert i := by
  apply Classical.byContradiction
  intro hi
  have e := replay (single i) (fun _ => false) (verifier (cert i)) (by
    intro u hu
    have ne : u ≠ i := fun eq => hi (eq ▸ hu)
    simp [single, ne])
  have hf := congrArg Prod.snd e
  rw [accept i, empty] at hf
  contradiction

/-- Each unordered pair forces a cross-query on at least one singleton
execution. Certificates may coincide and their transcripts may be adaptive. -/
theorem singleton_pair_cover
    (empty : ∀ c, (run (fun _ => false) (verifier c)).2 = false)
    (accept : ∀ i, (run (single i) (verifier (cert i))).2 = true)
    (unique : ∀ i j, i ≠ j → ∀ c d,
      (run (pair i j) (verifier c)).2 = true →
      (run (pair i j) (verifier d)).2 = true → c = d)
    (i j : ι) (different : i ≠ j) :
    j ∈ transcript verifier cert i ∨ i ∈ transcript verifier cert j := by
  by_cases hj : j ∈ transcript verifier cert i
  · exact Or.inl hj
  right
  apply Classical.byContradiction
  intro hi
  have ei := replay (single i) (pair i j) (verifier (cert i)) (by
    intro u hu
    have ne : u ≠ j := fun eq => hj (eq ▸ hu)
    simp [single, pair, ne])
  have ej := replay (single j) (pair i j) (verifier (cert j)) (by
    intro u hu
    have ne : u ≠ i := fun eq => hi (eq ▸ hu)
    simp [single, pair, ne])
  have eqCert := unique i j different _ _ (ei ▸ accept i) (ej ▸ accept j)
  have same : transcript verifier cert i = transcript verifier cert j := by
    unfold transcript
    rw [ei, ej, eqCert]
  have mem := queries_own_index verifier cert empty accept i
  exact hi (same ▸ mem)

private def sumOn (xs : List ι) (f : ι → Nat) := (xs.map f).sum

omit [DecidableEq ι] in
private theorem sum_cons (i : ι) (xs : List ι) (f : ι → Nat) :
    sumOn (i :: xs) f = f i + sumOn xs f := by simp [sumOn]

omit [DecidableEq ι] in
private theorem sum_add (xs : List ι) (f g : ι → Nat) :
    sumOn xs (fun i => f i + g i) = sumOn xs f + sumOn xs g := by
  induction xs with
  | nil => simp [sumOn]
  | cons a l ih => simp only [sum_cons, ih]; omega

omit [DecidableEq ι] in
private theorem sum_mono (xs : List ι) (f g : ι → Nat)
    (h : ∀ u ∈ xs, f u ≤ g u) : sumOn xs f ≤ sumOn xs g := by
  induction xs with
  | nil => simp [sumOn]
  | cons a l ih =>
    simp only [sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih (fun u hu => h u (by simp [hu])))

omit [DecidableEq ι] in
private theorem sum_const (xs : List ι) (k : Nat) :
    sumOn xs (fun _ => k) = xs.length * k := by
  induction xs with
  | nil => simp [sumOn]
  | cons a l ih => simp [sum_cons, ih, Nat.add_mul, Nat.add_comm]

omit [DecidableEq ι] in
private theorem sum_swap (xs ys : List ι) (f : ι → ι → Nat) :
    sumOn xs (fun i => sumOn ys (f i)) =
      sumOn ys (fun j => sumOn xs (fun i => f i j)) := by
  induction xs with
  | nil =>
    change 0 = sumOn ys (fun _ => 0)
    simp [sum_const]
  | cons a l ih => simp only [sum_cons, sum_add, ih]

private theorem sum_indicator (xs : List ι) (uniqueNames : xs.Nodup) (u : ι) :
    sumOn xs (fun j => if u = j then 1 else 0) = if u ∈ xs then 1 else 0 := by
  induction xs with
  | nil => simp [sumOn]
  | cons a l ih =>
    have h := List.nodup_cons.mp uniqueNames
    by_cases eq : u = a
    · subst u; simp [sum_cons, ih h.2, h.1]
    · simp [sum_cons, ih h.2, eq]

private def hits (row : List ι) (j : ι) : Nat :=
  match row with
  | [] => 0
  | a :: xs => (if a = j then 1 else 0) + hits xs j

private theorem positive_hit {row : List ι} {j : ι} (present : j ∈ row) : 1 ≤ hits row j := by
  induction row with
  | nil => simp at present
  | cons a xs ih =>
    rcases List.mem_cons.mp present with eq | tail
    · subst a; simp [hits]
    · have lower := ih tail
      simp only [hits]
      omega

private theorem sum_hits (xs row : List ι) (uniqueNames : xs.Nodup) :
    sumOn xs (hits row) ≤ row.length := by
  induction row with
  | nil => simp [hits, sum_const]
  | cons a l ih =>
    simp only [hits, sum_add, sum_indicator xs uniqueNames, List.length_cons]
    split <;> omega

/-- A family of query lists which contains its diagonal and covers each
off-diagonal pair has worst-case length at least ceil((M+1)/2). -/
theorem pair_cover_count (indices : List ι) (names : indices.Nodup)
    (nonempty : 0 < indices.length) (row : ι → List ι) (q : Nat)
    (own : ∀ i ∈ indices, i ∈ row i)
    (cover : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j → j ∈ row i ∨ i ∈ row j)
    (cap : ∀ i ∈ indices, (row i).length ≤ q) :
    indices.length + 1 ≤ 2*q := by
  let d := fun i j => hits (row i) j
  have cell (i j : ι) (hi : i ∈ indices) (hj : j ∈ indices) :
      1 + (if i = j then 1 else 0) ≤ d i j + d j i := by
    by_cases eq : i = j
    · subst j
      have pos := positive_hit (own i hi)
      simpa [d] using Nat.add_le_add pos pos
    · simp only [if_neg eq, Nat.add_zero, d]
      rcases cover i hi j hj eq with h | h
      · have pos := positive_hit h; omega
      · have pos := positive_hit h; omega
  have each (i : ι) (hi : i ∈ indices) :
      indices.length + 1 ≤ sumOn indices (fun j => d i j + d j i) := by
    have h := sum_mono indices _ _ (fun j hj => cell i j hi hj)
    simpa [sum_add, sum_const, sum_indicator indices names, hi] using h
  have lower := sum_mono indices _ _ each
  have upper := sum_mono indices _ _ (fun i hi =>
    Nat.le_trans (sum_hits indices (row i) names) (cap i hi))
  have tr := sum_swap indices indices d
  simp only [sum_const, sum_add] at lower upper
  change sumOn indices (fun i => sumOn indices (d i)) ≤ indices.length * q at upper
  rw [← tr] at lower
  have m := Nat.add_le_add upper upper
  have prod : indices.length * (indices.length + 1) ≤ indices.length * (2*q) := by
    rw [Nat.two_mul, Nat.mul_add indices.length q q]
    exact Nat.le_trans lower m
  exact Nat.le_of_mul_le_mul_left prod nonempty

theorem verifier_query_bound (indices : List ι) (names : indices.Nodup)
    (nonempty : 0 < indices.length) (q : Nat)
    (empty : ∀ c, (run (fun _ => false) (verifier c)).2 = false)
    (accept : ∀ i, (run (single i) (verifier (cert i))).2 = true)
    (unique : ∀ i j, i ≠ j → ∀ c d,
      (run (pair i j) (verifier c)).2 = true →
      (run (pair i j) (verifier d)).2 = true → c = d)
    (cap : ∀ i ∈ indices, (transcript verifier cert i).length ≤ q) :
    indices.length + 1 ≤ 2*q :=
  pair_cover_count indices names nonempty _ q
    (fun i _ => queries_own_index verifier cert empty accept i)
    (fun i _ j _ => singleton_pair_cover verifier cert empty accept unique i j) cap

end

section Tournament

/-- Predecessors in a cyclic tournament on 2r+1 positions. For an even
universe size the final dummy position is filtered out before any query. -/
private def predecessors (r i : Nat) : List Nat :=
  (List.range r).map (fun k =>
    if k + 1 ≤ i then i - (k+1) else 2*r+1+i-(k+1))

private theorem predecessor_iff {r i j : Nat} (_hi : i < 2*r+1) (hj : j < 2*r+1) :
    j ∈ predecessors r i ↔ (j < i ∧ i-j ≤ r) ∨ (i < j ∧ r < j-i) := by
  simp only [predecessors, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, e⟩
    split at e <;> omega
  · rintro (h | h)
    · refine ⟨i-j-1, by omega, ?_⟩
      split <;> omega
    · refine ⟨2*r+1+i-j-1, by omega, ?_⟩
      split <;> omega

private def opponents (m i : Nat) :=
  (predecessors (m/2) i).filter (fun j => decide (j < m))

private theorem orientation {m i j : Nat} (hi : i < m) (hj : j < m) (ne : i ≠ j) :
    (j ∈ opponents m i) ↔ (i ∉ opponents m j) := by
  simp only [opponents, List.mem_filter, decide_eq_true_eq, hi, hj, and_true]
  rw [predecessor_iff (by omega) (by omega), predecessor_iff (by omega) (by omega)]
  omega

private theorem no_self {m i : Nat} (hi : i < m) : i ∉ opponents m i := by
  simp only [opponents, List.mem_filter, decide_eq_true_eq, hi, and_true]
  rw [predecessor_iff (by omega) (by omega)]
  omega

private def allAbsent : List Nat → Queries Nat
  | [] => .halt true
  | a::xs => .ask a (allAbsent xs) (.halt false)

private theorem allAbsent_spec (w : Nat → Bool) (xs : List Nat) :
    (run w (allAbsent xs)).2 = true ↔ ∀ j ∈ xs, w j = false := by
  induction xs with
  | nil => simp [allAbsent, run]
  | cons a tl ih => cases ha : w a <;> simp [allAbsent, run, ha, ih]

private theorem allAbsent_cost (w : Nat → Bool) (xs : List Nat) :
    (run w (allAbsent xs)).1.length ≤ xs.length := by
  induction xs with
  | nil => simp [allAbsent, run]
  | cons a tl ih => cases ha : w a <;> simp [allAbsent, run, ha, ih]

def tournamentVerifier (m i : Nat) : Queries Nat :=
  if i < m then .ask i (.halt false) (allAbsent (opponents m i)) else .halt false

private theorem tournament_spec (w : Nat → Bool) {m i : Nat} :
    (run w (tournamentVerifier m i)).2 = true ↔
      i < m ∧ w i = true ∧ ∀ j ∈ opponents m i, w j = false := by
  by_cases hi : i < m
  · cases h : w i <;> simp [tournamentVerifier, hi, run, h, allAbsent_spec]
  · simp [tournamentVerifier, hi, run]

theorem tournament_cost (w : Nat → Bool) (m i : Nat) :
    (run w (tournamentVerifier m i)).1.length ≤ m/2+1 := by
  have h := allAbsent_cost w (opponents m i)
  have hl : (opponents m i).length ≤ m/2 := by
    refine Nat.le_trans (List.length_filter_le ..) ?_
    simp [predecessors]
  by_cases hi : i < m
  · cases hw : w i <;> simp [tournamentVerifier, hi, run, hw] <;> omega
  · simp [tournamentVerifier, hi, run]

theorem tournament_empty (m c : Nat) :
    (run (fun _ => false) (tournamentVerifier m c)).2 = false := by
  cases h : (run (fun _ => false) (tournamentVerifier m c)).2 with
  | false => rfl
  | true =>
    have a := (tournament_spec _).mp h
    simp at a

theorem tournament_singleton {m i : Nat} (hi : i < m) (c : Nat) :
    (run (single i) (tournamentVerifier m c)).2 = true ↔ c = i := by
  rw [tournament_spec]
  constructor
  · intro h; simpa [single] using h.2.1
  · rintro rfl
    refine ⟨hi, by simp [single], ?_⟩
    intro j hj
    have hne : j ≠ c := fun e => no_self hi (e ▸ hj)
    simp [single, hne]

private theorem tournament_pair_spec {m i j : Nat} (hi : i < m) (_ne : i ≠ j) :
    (run (pair i j) (tournamentVerifier m i)).2 = true ↔ j ∉ opponents m i := by
  rw [tournament_spec]
  constructor
  · intro h hj
    have abs := h.2.2 j hj
    simp [pair] at abs
  · intro h
    refine ⟨hi, by simp [pair], ?_⟩
    intro u hu
    have a : u ≠ i := fun e => no_self hi (e ▸ hu)
    have b : u ≠ j := fun e => h (e ▸ hu)
    simp [pair, a, b]

/-- Exactly one certificate accepts a nonempty two-element oracle. -/
theorem tournament_pair {m i j : Nat} (hi : i < m) (hj : j < m) (ne : i ≠ j) :
    ∃ c, (run (pair i j) (tournamentVerifier m c)).2 = true ∧
      ∀ e, (run (pair i j) (tournamentVerifier m e)).2 = true → e = c := by
  have left := tournament_pair_spec hi ne
  have right := tournament_pair_spec hj (Ne.symm ne)
  have sw : pair i j = pair j i := by funext u; simp [pair, or_comm]
  rw [← sw] at right
  have candidates (e : Nat) (h : (run (pair i j) (tournamentVerifier m e)).2 = true) :
      e = i ∨ e = j := by
    simpa [pair] using ((tournament_spec _).mp h).2.1
  by_cases h : j ∈ opponents m i
  · have a := right.mpr ((orientation hi hj ne).mp h)
    refine ⟨j, a, fun e he => ?_⟩
    rcases candidates e he with eq | eq
    · subst e; exact False.elim (left.mp he h)
    · exact eq
  · have hx : i ∈ opponents m j := (orientation hj hi (Ne.symm ne)).mpr h
    refine ⟨i, left.mpr h, fun e he => ?_⟩
    rcases candidates e he with eq | eq
    · exact eq
    · subst e; exact False.elim (right.mp he hx)

end Tournament
end TwoWitnessIsolation
