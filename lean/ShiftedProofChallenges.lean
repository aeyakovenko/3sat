import Std

namespace ShiftedProofChallenges

/-- A binary challenge with exactly `n` bits. -/
def Cube : Nat → Type
  | 0 => Unit
  | n + 1 => Bool × Cube n

def translate : (n : Nat) → Cube n → Cube n → Cube n
  | 0, _, _ => ()
  | n + 1, (a, x), (b, y) => (a ^^ b, translate n x y)

/-- Unnormalized uniform sum on challenges. -/
def mass : (n : Nat) → (Cube n → Nat) → Nat
  | 0, f => f ()
  | n + 1, f => mass n (fun x => f (false, x)) + mass n (fun x => f (true, x))

theorem translation_mass (n : Nat) (a : Cube n) (f : Cube n → Nat) :
    mass n (fun x => f (translate n a x)) = mass n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b, a'⟩ := a
    cases b <;> simp only [mass, translate, Bool.false_xor, Bool.true_xor,
      Bool.not_true, Bool.not_false, ih a' (fun x => f (false, x)),
      ih a' (fun x => f (true, x)), Nat.add_comm]

theorem mass_add (n : Nat) (f g : Cube n → Nat) :
    mass n (fun x => f x + g x) = mass n f + mass n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mass, ih (fun x => f (false, x)) (fun x => g (false, x)),
      ih (fun x => f (true, x)) (fun x => g (true, x))]
    omega

theorem mass_scale (n c : Nat) (f : Cube n → Nat) :
    mass n (fun x => c * f x) = c * mass n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mass, ih (fun x => f (false, x)), ih (fun x => f (true, x)), Nat.mul_add]

theorem mass_constant (n c : Nat) : mass n (fun _ => c) = 2^n * c := by
  induction n with
  | zero => simp [mass]
  | succ n ih => simp [mass, ih, Nat.pow_succ, Nat.mul_two, Nat.add_mul]

theorem mass_strict (n : Nat) (f g : Cube n → Nat) (lt : ∀ x, f x < g x) :
    mass n f < mass n g := by
  induction n with
  | zero => exact lt ()
  | succ n ih =>
    exact Nat.add_lt_add (ih _ _ (fun x => lt (false, x))) (ih _ _ (fun x => lt (true, x)))

def hits (n : Nat) (f : Cube n → Nat) (shift : Cube n) : List (Cube n) → Nat
  | [] => 0
  | a :: as => f (translate n a shift) + hits n f shift as

/-- Repetitions in the batch and dependence of `f` on the fixed batch are allowed. -/
theorem batch_shift_mass (n : Nat) (f : Cube n → Nat) (batch : List (Cube n)) :
    mass n (fun shift => hits n f shift batch) = batch.length * mass n f := by
  induction batch with
  | nil => simp [hits, mass_constant]
  | cons a as ih =>
    simp only [hits, List.length_cons, Nat.succ_mul]
    rw [mass_add n (fun shift => f (translate n a shift)) (fun shift => hits n f shift as),
      translation_mass, ih, Nat.add_comm]

theorem exists_good_shift (n : Nat) (f : Cube n → Nat) (batch : List (Cube n)) :
    ∃ shift, batch.length * mass n f ≤ 2^n * hits n f shift batch := by
  apply Classical.byContradiction
  intro h
  have bad (x : Cube n) : 2^n * hits n f x batch < batch.length * mass n f :=
    Nat.lt_of_not_ge (fun hx => h ⟨x, hx⟩)
  have less := mass_strict n _ _ bad
  rw [mass_scale n (2^n) (fun shift => hits n f shift batch),
    batch_shift_mass, mass_constant] at less
  exact Nat.lt_irrefl _ less

/-- Fixing the verifier's coins gives this finite adaptive binary query tree. -/
inductive Query where
  | raw (address : Nat)
  | proof (address : Nat)

inductive Checker where
  | stop (accepted : Bool)
  | read (query : Query) (next : Bool → Checker)

def reply (raw proof : Nat → Bool) : Query → Bool
  | .raw j => raw j
  | .proof j => proof j

def verdict (raw proof : Nat → Bool) : Checker → Bool
  | .stop b => b
  | .read q next => verdict raw proof (next (reply raw proof q))

def asked (raw proof : Nat → Bool) : Checker → List Query
  | .stop _ => []
  | .read q next => q :: asked raw proof (next (reply raw proof q))

/-- Every unequal verdict forces an incorrect proof response at a real honest slot. -/
theorem honest_disagreement (raw honest candidate : Nat → Bool) (tree : Checker)
    (different : verdict raw honest tree ≠ verdict raw candidate tree) :
    ∃ j, Query.proof j ∈ asked raw honest tree ∧ honest j ≠ candidate j := by
  induction tree with
  | stop b => exact False.elim (different rfl)
  | read q next ih =>
    cases q with
    | raw a =>
      obtain ⟨j, occurs, mismatch⟩ := ih (raw a) different
      exact ⟨j, List.mem_cons_of_mem _ occurs, mismatch⟩
    | proof a =>
      by_cases same : honest a = candidate a
      · have diff : verdict raw honest (next (honest a)) ≠ verdict raw candidate (next (honest a)) := by
          simpa only [verdict, reply, ← same] using different
        obtain ⟨j, occurs, mismatch⟩ := ih (honest a) diff
        exact ⟨j, List.mem_cons_of_mem _ occurs, mismatch⟩
      · exact ⟨a, List.mem_cons_self, same⟩

def shadow : Checker → List Bool → List Query
  | .stop _, _ => []
  | .read _ _, [] => []
  | .read q next, bit :: rest => q :: shadow (next bit) rest

/-- Padding the actual answer transcript arbitrarily still reproduces every honest slot in the
    public simulation, which receives only the supplied bits and has no genuine oracle. -/
theorem shadow_honest (raw honest : Nat → Bool) (tree : Checker) (padding : List Bool) :
    shadow tree ((asked raw honest tree).map (reply raw honest) ++ padding) = asked raw honest tree := by
  induction tree with
  | stop b => rfl
  | read q next ih =>
    simp only [asked, List.map_cons, List.cons_append, shadow, ih]

end ShiftedProofChallenges
