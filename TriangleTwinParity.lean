import Std

namespace TriangleTwinParity

def total {X : Type} : List X → (X → Nat) → Nat
  | [], _ => 0
  | x :: xs, f => f x + total xs f

private theorem total_add {X : Type} (xs : List X) (f g : X → Nat) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [total, ih]; omega

/-- The two vertex profiles are labeled and range independently over the
same finite list. Swapping unequal profiles cancels them modulo two. -/
theorem symmetric_pairs {X : Type} (xs : List X) (w : X → X → Nat)
    (sym : ∀ x y, w x y = w y x) :
    total xs (fun x => total xs (w x)) % 2 =
      total xs (fun x => w x x) % 2 := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    change ((w p p + total ps (w p)) +
      total ps (fun x => w x p + total ps (w x))) % 2 =
      (w p p + total ps (fun x => w x x)) % 2
    rw [total_add]
    have pair : (fun x => w x p) = w p := funext fun x => sym x p
    rw [pair]
    omega

structure Graph (A B C : Type) where
  ab : A → B → Bool
  bc : B → C → Bool
  ca : C → A → Bool

structure Profile (B C : Type) where
  toB : B → Bool
  fromC : C → Bool

def Triangle {A B C : Type} (g : Graph A B C) : Prop :=
  ∃ i k j, g.ab i k = true ∧ g.bc k j = true ∧ g.ca j i = true

def Works {A B C : Type} (p : Profile B C) (g : Graph A B C) : Prop :=
  ∃ k j, p.toB k = true ∧ g.bc k j = true ∧ p.fromC j = true

/-- Attach a new vertex in the first part. All its incident edges form one profile. -/
def attach {A B C : Type} (g : Graph A B C) (p : Profile B C) : Graph (Option A) B C where
  ab i k := match i with | none => p.toB k | some a => g.ab a k
  bc := g.bc
  ca j i := match i with | none => p.fromC j | some a => g.ca j a

def erase {A B C : Type} (g : Graph (Option A) B C) : Graph A B C where
  ab i k := g.ab (some i) k
  bc := g.bc
  ca j i := g.ca j (some i)

def incident {A B C : Type} (g : Graph (Option A) B C) : Profile B C where
  toB := g.ab none
  fromC j := g.ca j none

theorem erase_attach {A B C : Type} (g : Graph A B C) (p : Profile B C) :
    erase (attach g p) = g ∧ incident (attach g p) = p := by
  exact ⟨rfl, rfl⟩

/-- Every labeled extension has precisely the retained graph and profile
given by erase and incident. This is the enumeration behind the pair sum. -/
theorem attach_erase {A B C : Type} (g : Graph (Option A) B C) :
    attach (erase g) (incident g) = g := by
  cases g with
  | mk ab bc ca =>
    have first : (fun i k => match i with | none => ab none k | some a => ab (some a) k) = ab :=
      funext fun i => funext fun k => by cases i <;> rfl
    have third : (fun j i => match i with | none => ca j none | some a => ca j (some a)) = ca :=
      funext fun j => funext fun i => by cases i <;> rfl
    exact (congrArg (fun f => Graph.mk f bc _) first).trans
      (congrArg (fun h => Graph.mk ab bc h) third)

theorem triangle_attach {A B C : Type} (g : Graph A B C) (p : Profile B C) :
    Triangle (attach g p) ↔ Triangle g ∨ Works p g := by
  constructor
  · rintro ⟨i,k,j,edges⟩
    cases i with
    | none => exact Or.inr ⟨k,j,edges⟩
    | some a => exact Or.inl ⟨a,k,j,edges⟩
  · rintro (⟨i,k,j,edges⟩ | ⟨k,j,edges⟩)
    · exact ⟨some i,k,j,edges⟩
    · exact ⟨none,k,j,edges⟩

theorem swap_profiles {A B C : Type} (g : Graph A B C) (p q : Profile B C) :
    Triangle (attach (attach g p) q) ↔ Triangle (attach (attach g q) p) := by
  simp only [triangle_attach]
  change (Triangle g ∨ Works p g) ∨ Works q g ↔ (Triangle g ∨ Works q g) ∨ Works p g
  rw [or_assoc, or_assoc]
  exact or_congr_right or_comm

theorem triangle_delete_twin {A B C : Type} (g : Graph A B C) (p : Profile B C) :
    Triangle (attach (attach g p) p) ↔ Triangle (attach g p) := by
  simp only [triangle_attach]
  change (Triangle g ∨ Works p g) ∨ Works p g ↔ Triangle g ∨ Works p g
  simp only [or_assoc, or_self]

noncomputable def verdictWeight {A B C : Type} (g : Graph A B C) (positive : Bool) : Nat := by
  classical
  exact if decide (Triangle g) = positive then 1 else 0

private theorem same_verdict {A A' B C : Type} {g : Graph A B C} {h : Graph A' B C}
    (same : Triangle g ↔ Triangle h) (positive : Bool) :
    verdictWeight g positive = verdictWeight h positive := by
  classical
  simp [verdictWeight, propext same]

theorem shrink_first_part {A B C : Type} (g : Graph A B C) (ps : List (Profile B C))
    (positive : Bool) :
    total ps (fun p => total ps (fun q => verdictWeight (attach (attach g p) q) positive)) % 2 =
      total ps (fun p => verdictWeight (attach g p) positive) % 2 := by
  rw [symmetric_pairs ps _ (fun p q => same_verdict (swap_profiles g p q) positive)]
  have diag : (fun p => verdictWeight (attach (attach g p) p) positive) =
      (fun p => verdictWeight (attach g p) positive) :=
    funext fun p => same_verdict (triangle_delete_twin g p) positive
  rw [diag]

/-- A transcript fixes exactly the values it reads. Each none is one
unread independent physical bit; a read word can specify several bits. -/
def completions : List (Option Bool) → List (List Bool)
  | [] => [[]]
  | some b :: xs => (completions xs).map (b :: ·)
  | none :: xs => (completions xs).map (false :: ·) ++ (completions xs).map (true :: ·)

def freeBits : List (Option Bool) → Nat
  | [] => 0
  | some _ :: xs => freeBits xs
  | none :: xs => freeBits xs + 1

theorem number_completions (xs : List (Option Bool)) :
    (completions xs).length = 2 ^ freeBits xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp [completions, freeBits, ih, Nat.pow_succ] <;> omega

/-- Applied separately to the list of full transcripts of each verdict.
A disjoint partition is what identifies the sum with the input count. -/
theorem singleton_parity (leaves : List (List (Option Bool))) :
    total leaves (fun xs => (completions xs).length) % 2 =
      leaves.countP (fun xs => freeBits xs == 0) % 2 := by
  induction leaves with
  | nil => rfl
  | cons xs rest ih =>
    simp only [total, number_completions, List.countP_cons] at *
    cases n : freeBits xs with
    | zero => simp [n]; omega
    | succ k => simp [n, Nat.pow_succ]; omega

theorem odd_full_transcript (leaves : List (List (Option Bool)))
    (odd : total leaves (fun xs => (completions xs).length) % 2 = 1) :
    ∃ xs ∈ leaves, freeBits xs = 0 := by
  rw [singleton_parity] at odd
  have positive : 0 < leaves.countP (fun xs => freeBits xs == 0) := by omega
  simpa using (List.countP_pos_iff.mp positive)

/-- Orient each matched one-bit edge by the parity of its input; the two
entries are respectively the verdicts on the even and the odd input. -/
abbrev PairVerdicts := Bool × Bool

def signedContribution (p : PairVerdicts) : Int :=
  (if p.1 then 1 else 0) - (if p.2 then 1 else 0)

def signedTotal : List PairVerdicts → Int
  | [] => 0
  | p :: ps => signedContribution p + signedTotal ps

def upward (p : PairVerdicts) := p.1 && !p.2
def downward (p : PairVerdicts) := !p.1 && p.2
def pivotal (p : PairVerdicts) := p.1 != p.2

/-- Equal verdicts on a pair cancel. Pivotal pairs contribute +1 or -1.
The exact difference also gives a parity constraint on their number. -/
theorem signed_counts (ps : List PairVerdicts) :
    signedTotal ps = (ps.countP upward : Int) - (ps.countP downward : Int) ∧
    ps.countP pivotal = ps.countP upward + ps.countP downward := by
  induction ps with
  | nil => simp [signedTotal]
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    rcases ih with ⟨sig, piv⟩
    cases a <;> cases b <;>
      simp only [signedTotal, List.countP_cons, signedContribution, upward,
        downward, pivotal, sig, piv] <;> simp <;> omega

theorem signed_pivotal_bounds (ps : List PairVerdicts) :
    -(ps.countP pivotal : Int) ≤ signedTotal ps ∧
    signedTotal ps ≤ (ps.countP pivotal : Int) ∧
    signedTotal ps % 2 = (ps.countP pivotal : Int) % 2 := by
  obtain ⟨sig,piv⟩ := signed_counts ps
  omega

end TriangleTwinParity
