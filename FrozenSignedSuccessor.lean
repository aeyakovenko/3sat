import Std

namespace FrozenSignedSuccessor

variable {Block Aux : Type}

def parity (flip : Block → Bool) : List Block → Bool
  | [] => false
  | b :: bs => flip b ^^ parity flip bs

/-- Each witness item records an outgoing boundary bit and the private auxiliary data. -/
def Chain (gate : Block → Bool → Bool → Aux → Prop) :
    List Block → Bool → Bool → List (Bool × Aux) → Prop
  | [], input, output, witness => output = input ∧ witness = []
  | _ :: _, _, _, [] => False
  | b :: bs, input, output, (mid,aux) :: rest =>
    gate b input mid aux ∧ Chain gate bs mid output rest

def canonical (flip : Block → Bool) (inside : Block → Bool → Aux) :
    List Block → Bool → List (Bool × Aux)
  | [], _ => []
  | b :: bs, input =>
    let mid := input ^^ flip b
    (mid, inside b input) :: canonical flip inside bs mid

/-- With the pins fixed, a correct endpoint has precisely its canonical full extension. -/
theorem chain_exact (gate : Block → Bool → Bool → Aux → Prop)
    (flip : Block → Bool) (inside : Block → Bool → Aux)
    (localRule : ∀ b input mid aux, gate b input mid aux ↔
      mid = (input ^^ flip b) ∧ aux = inside b input)
    (blocks : List Block) (input output : Bool) (witness : List (Bool × Aux)) :
    Chain gate blocks input output witness ↔
      output = (input ^^ parity flip blocks) ∧ witness = canonical flip inside blocks input := by
  induction blocks generalizing input witness with
  | nil => simp [Chain, canonical, parity]
  | cons b bs ih =>
    cases witness with
    | nil => simp [Chain, canonical]
    | cons item rest =>
      rcases item with ⟨mid,aux⟩
      simp only [Chain, canonical, parity, localRule, ih, List.cons.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨rfl,rfl⟩,h,rfl⟩
        exact ⟨by simpa [Bool.xor_assoc] using h, ⟨rfl,rfl⟩,rfl⟩
      · rintro ⟨h,⟨rfl,rfl⟩,rfl⟩
        exact ⟨⟨rfl,rfl⟩,by simpa [Bool.xor_assoc] using h,rfl⟩

theorem exists_extension (gate : Block → Bool → Bool → Aux → Prop)
    (flip : Block → Bool) (inside : Block → Bool → Aux)
    (localRule : ∀ b input mid aux, gate b input mid aux ↔
      mid = (input ^^ flip b) ∧ aux = inside b input)
    (blocks : List Block) (input output : Bool) :
    (∃ witness, Chain gate blocks input output witness) ↔ output = (input ^^ parity flip blocks) := by
  constructor
  · rintro ⟨w,hw⟩
    exact ((chain_exact gate flip inside localRule blocks input output w).mp hw).1
  · intro h
    exact ⟨_,(chain_exact gate flip inside localRule blocks input output _).mpr ⟨h,rfl⟩⟩

theorem parity_append (flip : Block → Bool) (xs ys : List Block) :
    parity flip (xs ++ ys) = (parity flip xs ^^ parity flip ys) := by
  induction xs with
  | nil => simp [parity]
  | cons x tail ih => simp [parity, ih, Bool.xor_assoc]

/-- Appending any successor retains every old junction and private witness at the front. -/
theorem canonical_append (flip : Block → Bool) (inside : Block → Bool → Aux)
    (xs ys : List Block) (input : Bool) :
    canonical flip inside (xs ++ ys) input =
    canonical flip inside xs input ++ canonical flip inside ys (input ^^ parity flip xs) := by
  induction xs generalizing input with
  | nil => simp [canonical, parity]
  | cons x tail ih => simp [canonical, parity, ih, Bool.xor_assoc]

/-- Changing one signed block to one with the opposite toggle reverses satisfiability
    at every pair of fixed outer endpoint values. -/
theorem flip_one_pin (gate : Block → Bool → Bool → Aux → Prop)
    (flip : Block → Bool) (inside : Block → Bool → Aux)
    (localRule : ∀ b input mid aux, gate b input mid aux ↔
      mid = (input ^^ flip b) ∧ aux = inside b input)
    (left right : List Block) (b c : Block) (opposite : flip c = !(flip b))
    (input output : Bool) :
    (∃ w, Chain gate (left ++ c :: right) input output w) ↔
    ¬ ∃ w, Chain gate (left ++ b :: right) input output w := by
  simp only [exists_extension gate flip inside localRule, parity_append, parity, opposite]
  cases input <;> cases output <;> cases parity flip left <;> cases parity flip right <;>
    cases flip b <;> decide

/-- A deterministic read tree. The continuation may depend on the whole word returned. -/
inductive ReadTree (Word : Type) where
  | done (answer : Bool)
  | read (address : Nat) (next : Word → ReadTree Word)

def ReadTree.run {Word : Type} (input : Nat → Word) : ReadTree Word → Bool × List Nat
  | .done answer => (answer,[])
  | .read address next =>
    let rest := (next (input address)).run input
    (rest.1, address :: rest.2)

theorem different_answer_reads_address {Word : Type} (tree : ReadTree Word)
    (a b : Nat → Word) (p : Nat) (same : ∀ j, j ≠ p → a j = b j)
    (changed : (tree.run a).1 ≠ (tree.run b).1) : p ∈ (tree.run a).2 := by
  induction tree with
  | done answer => exact False.elim (changed rfl)
  | read address next ih =>
    by_cases atPin : address = p
    · simp [ReadTree.run, atPin]
    · have nextDiff : ((next (a address)).run a).1 ≠ ((next (a address)).run b).1 := by
        simpa only [ReadTree.run, ← same address atPin] using changed
      exact List.mem_cons_of_mem _ (ih (a address) nextDiff)

/-- All distinct single-word-sensitive sites must occur on one genuine execution. -/
theorem sensitive_word_count {Word : Type} (tree : ReadTree Word) (a : Nat → Word)
    (sites : List Nat) (distinct : sites.Nodup)
    (edits : ∀ p ∈ sites, ∃ b, (∀ j, j ≠ p → a j = b j) ∧
      (tree.run a).1 ≠ (tree.run b).1) : sites.length ≤ (tree.run a).2.length := by
  have covered : ∀ p ∈ sites, p ∈ (tree.run a).2 := by
    intro p hp
    obtain ⟨b,same,changed⟩ := edits p hp
    exact different_answer_reads_address tree a b p same changed
  generalize (tree.run a).2 = reads at *
  clear edits
  induction sites generalizing reads with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp distinct
    have hp := covered p (by simp)
    have hpos := List.length_pos_of_mem hp
    have remaining := ih tail (reads.erase p) (by
      intro j hj
      have hne : j ≠ p := fun eq => fresh (eq ▸ hj)
      exact (List.mem_erase_of_ne hne).2 (covered j (by simp [hj])))
    rw [List.length_erase_of_mem hp] at remaining
    simp
    omega

end FrozenSignedSuccessor
