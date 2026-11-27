import Std

namespace ParityChainChecks

/-- The pair of equality or disequality clauses, evaluated at its boundary bits. -/
def localClauses (charge previous nextBit : Bool) : Bool :=
  if charge then (previous || nextBit) && (!previous || !nextBit)
  else (!previous || nextBit) && (previous || !nextBit)

theorem localClauses_exact (charge previous nextBit : Bool) :
    localClauses charge previous nextBit = true ↔
      nextBit = Bool.xor previous charge := by
  cases charge <;> cases previous <;> cases nextBit <;> decide

def chain (charges : List Bool) (left right : Bool) : Prop :=
  match charges with
  | [] => right = left
  | x :: xs => ∃ b, localClauses x left b = true ∧ chain xs b right

theorem chain_exact (xs : List Bool) (left right : Bool) :
    chain xs left right ↔ right = Bool.xor left (xs.foldr Bool.xor false) := by
  induction xs generalizing left with
  | nil => cases left <;> simp [chain]
  | cons x xs ih =>
    simp only [chain, localClauses_exact, ih, List.foldr_cons, exists_eq_left]
    cases left <;> cases x <;> cases xs.foldr Bool.xor false <;> rfl

theorem zero_endpoints (xs : List Bool) :
    chain xs false false ↔ xs.foldr Bool.xor false = false := by
  rw [chain_exact]
  cases xs.foldr Bool.xor false <;> decide

inductive QueryTree (ι : Type)
  | leaf (answer : Bool)
  | query (index : ι) (zeros ones : QueryTree ι)

def QueryTree.eval (x : ι → Bool) : QueryTree ι → Bool
  | .leaf b => b
  | .query i l r => if x i then r.eval x else l.eval x

def QueryTree.depth : QueryTree ι → Nat
  | .leaf _ => 0
  | .query _ l r => max l.depth r.depth + 1

/-- The partial assignments on paths to rejection. Repeated queries are allowed. -/
def QueryTree.badPaths : QueryTree ι → List (List (ι × Bool))
  | .leaf true => []
  | .leaf false => [[]]
  | .query i l r =>
    l.badPaths.map ((i, false) :: ·) ++ r.badPaths.map ((i, true) :: ·)

def agreesOn (x : ι → Bool) (p : List (ι × Bool)) : Prop :=
  ∀ z ∈ p, x z.1 = z.2

theorem agreesOn_cons (x : ι → Bool) (p : List (ι × Bool)) (i : ι) (b : Bool) :
    agreesOn x ((i,b)::p) ↔ x i = b ∧ agreesOn x p := by
  simp [agreesOn]

theorem rejects_iff_matching_path (t : QueryTree ι) (x : ι → Bool) :
    t.eval x = false ↔ ∃ p ∈ t.badPaths, agreesOn x p := by
  induction t with
  | leaf b => cases b <;> simp [QueryTree.eval, QueryTree.badPaths, agreesOn]
  | query i l r ihl ihr =>
    have branches :
        (∃ p ∈ (QueryTree.query i l r).badPaths, agreesOn x p) ↔
          (x i = false ∧ ∃ p ∈ l.badPaths, agreesOn x p) ∨
          (x i = true ∧ ∃ p ∈ r.badPaths, agreesOn x p) := by
      constructor
      · rintro ⟨p, mem, agree⟩
        simp only [QueryTree.badPaths, List.mem_append, List.mem_map] at mem
        rcases mem with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
        · obtain ⟨hi, tail⟩ := (agreesOn_cons ..).mp agree
          exact Or.inl ⟨hi, a, ha, tail⟩
        · obtain ⟨hi, tail⟩ := (agreesOn_cons ..).mp agree
          exact Or.inr ⟨hi, a, ha, tail⟩
      · rintro (⟨hi, p, hp, tail⟩ | ⟨hi, p, hp, tail⟩)
        · refine ⟨(i, false) :: p, ?_, (agreesOn_cons ..).mpr ⟨hi, tail⟩⟩
          exact List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
        · refine ⟨(i, true) :: p, ?_, (agreesOn_cons ..).mpr ⟨hi, tail⟩⟩
          exact List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
    rw [branches]
    cases h : x i <;> simp [QueryTree.eval, h, ihl, ihr]

theorem bad_path_width (t : QueryTree ι) (p : List (ι × Bool)) (h : p ∈ t.badPaths) :
    p.length ≤ t.depth := by
  induction t generalizing p with
  | leaf b =>
    cases b <;> simp [QueryTree.badPaths] at h
    subst p
    simp [QueryTree.depth]
  | query i l r ihl ihr =>
    simp only [QueryTree.badPaths, List.mem_append, List.mem_map] at h
    rcases h with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
    · have := ihl q hq
      simp only [List.length_cons, QueryTree.depth]
      omega
    · have := ihr q hq
      simp only [List.length_cons, QueryTree.depth]
      omega

/-- XOR of a vector of independently readable bits. -/
def parity (x : Fin n → Bool) : Bool :=
  (List.ofFn x).foldr Bool.xor false

/-- Each selected block is checked against its actual parity. -/
theorem two_messages (payload : Fin b → Fin k → Bool) (target : Bool) :
    (∃ claims : Fin b → Bool, parity claims = target ∧
      ∀ i, claims i = parity (payload i)) ↔
    parity (fun i => parity (payload i)) = target := by
  constructor
  · rintro ⟨claims, h, agree⟩
    simpa [funext agree] using h
  · intro h
    exact ⟨_, h, fun _ => rfl⟩

/-- An opposing list with a different parity must have a wrong coordinate. -/
theorem three_messages (payload : Fin b → Fin c → Fin k → Bool) (target : Bool) :
    (∃ claims : Fin b → Bool, parity claims = target ∧
      ∀ i (opposing : Fin c → Bool), parity opposing ≠ claims i →
        ∃ j, opposing j ≠ parity (payload i j)) ↔
    parity (fun i => parity (fun j => parity (payload i j))) = target := by
  classical
  constructor
  · rintro ⟨claims, h, challenge⟩
    have agree : ∀ i, claims i = parity (fun j => parity (payload i j)) := by
      intro i
      apply Classical.byContradiction
      intro bad
      have counter := challenge i (fun j => parity (payload i j)) (Ne.symm bad)
      obtain ⟨j, hj⟩ := counter
      exact hj rfl
    simpa [funext agree] using h
  · intro h
    refine ⟨_, h, ?_⟩
    intro i opposing different
    apply Classical.byContradiction
    intro noMistake
    apply different
    apply congrArg parity
    funext j
    apply Classical.byContradiction
    intro hj
    exact noMistake ⟨j, hj⟩

end ParityChainChecks
