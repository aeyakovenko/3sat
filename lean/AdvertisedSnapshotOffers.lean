import Std

namespace AdvertisedSnapshotOffers

/-- A fixed finite list of offers fails if every eligible decoder gives a wrong
    answer or times out somewhere. One address per offer suffices. An ineligible
    offer needs no address test, so its directory entry may contain the default. -/
theorem terminal_directory_iff {Addr Word : Type} (defaultAddress : Addr) (n : Nat)
    (eligible : Fin n → Bool) (reply : Fin n → Addr → Option Word) (actual : Addr → Word) :
    (∃ directory : Fin n → Addr, ∀ i, eligible i = false ∨
      reply i (directory i) ≠ some (actual (directory i))) ↔
      ¬ ∃ i, eligible i = true ∧ ∀ a, reply i a = some (actual a) := by
  constructor
  · rintro ⟨directory, failed⟩ ⟨i, included, truthful⟩
    rcases failed i with ineligible | mismatch
    · simp [included] at ineligible
    · exact mismatch (truthful (directory i))
  · intro noTruthful
    have each (i : Fin n) : ∃ a, eligible i = false ∨ reply i a ≠ some (actual a) := by
      cases hi : eligible i with
      | false => exact ⟨defaultAddress, Or.inl rfl⟩
      | true =>
        apply Classical.byContradiction
        intro noError
        apply noTruthful
        refine ⟨i, hi, fun a => ?_⟩
        exact Classical.byContradiction (fun bad => noError ⟨a, Or.inr bad⟩)
    exact ⟨fun i => Classical.choose (each i), fun i => Classical.choose_spec (each i)⟩

/-- The existential directory above has exactly one explicitly listed address per offer. -/
theorem directory_length {Addr : Type} {n : Nat} (directory : Fin n → Addr) :
    (List.ofFn directory).length = n := List.length_ofFn

/-- A checked header locates a packed bit string by its first word and its bit length. -/
structure Header where
  base : Nat
  length : Nat

structure View where
  length : Nat
  read : Nat → Bool

/-- Return zero beyond the advertised length. The caller fixes a positive word width. -/
def view (memory : Nat → Nat) (width : Nat) (h : Header) : View where
  length := h.length
  read i := if i < h.length then (memory (h.base + i / width)).testBit (i % width) else false

/-- Replayed endpoint memory may combine earlier decoded words and writes since the
    cut. A write of zero still overrides its base word. -/
def overlay (base : Nat → Nat) (writes : Nat → Option Nat) (a : Nat) : Nat :=
  (writes a).getD (base a)

theorem overlay_agrees (base actual : Nat → Nat) (writes : Nat → Option Nat)
    (untouched : ∀ a, writes a = none → base a = actual a)
    (written : ∀ a w, writes a = some w → w = actual a) :
    ∀ a, overlay base writes a = actual a := by
  intro a
  cases h : writes a with
  | none => simpa [overlay, h] using untouched a h
  | some w => simpa [overlay, h] using written a w h

/-- Header discovery may depend on both control and work memory. A malformed or
    inadmissible header gives no result. The decoder may query its packed input
    adaptively, while this interface exposes only that input to it. -/
def endpointReply {Control Offer : Type} (header : Control → (Nat → Nat) → Offer → Option Header)
    (decode : View → Nat → Option Nat) (width : Nat) (control : Control)
    (memory : Nat → Nat) (offer : Offer) (a : Nat) : Option Nat :=
  (header control memory offer).bind fun h => decode (view memory width h) a

/-- All-word endpoint agreement identifies the authentic headers, the values of
    the reconstructed code bits and the result of every bounded decoder call. -/
theorem endpoint_extraction {Control Offer : Type}
    (header : Control → (Nat → Nat) → Offer → Option Header) (decode : View → Nat → Option Nat)
    (width : Nat) (state realState : Control) (memory actual : Nat → Nat)
    (sameState : state = realState) (sameWord : ∀ a, memory a = actual a)
    (offer : Offer) :
    header state memory offer = header realState actual offer ∧
    (∀ h i, (view memory width h).read i = (view actual width h).read i) ∧
    ∀ a, endpointReply header decode width state memory offer a =
      endpointReply header decode width realState actual offer a := by
  have sameMemory : memory = actual := funext sameWord
  subst realState actual
  exact ⟨rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- Once arbitrary-address checking has established the endpoint's whole state,
    one chosen directory witnesses the absence of any truthful eligible offer in
    that actual state. Eligibility may itself inspect checked headers and words. -/
theorem replayed_directory_iff {Control : Type} (n : Nat)
    (eligible : Control → (Nat → Nat) → Fin n → Bool)
    (header : Control → (Nat → Nat) → Fin n → Option Header) (decode : View → Nat → Option Nat)
    (width : Nat) (state realState : Control) (memory actual : Nat → Nat)
    (sameState : state = realState) (sameWord : ∀ a, memory a = actual a) :
    (∃ d : Fin n → Nat, ∀ i, eligible state memory i = false ∨
      endpointReply header decode width state memory i (d i) ≠ some (memory (d i))) ↔
    ¬ ∃ i, eligible realState actual i = true ∧ ∀ a,
      endpointReply header decode width realState actual i a = some (actual a) := by
  have sameMemory : memory = actual := funext sameWord
  subst realState actual
  exact terminal_directory_iff 0 n (eligible state memory)
    (endpointReply header decode width state memory) memory

/-- The same endpoint argument permits an arbitrary fixed extractor returning an
    indexed view of the current code. In particular its individual bit answers
    may depend adaptively on several words of the reconstructed endpoint memory. -/
theorem arbitrary_extractor_directory {Control : Type} (n : Nat)
    (extract : Control → (Nat → Nat) → Fin n → Option View) (decode : View → Nat → Option Nat)
    (state realState : Control) (memory actual : Nat → Nat)
    (sameState : state = realState) (sameWord : ∀ a, memory a = actual a) :
    (∃ d : Fin n → Nat, ∀ i,
      (extract state memory i).bind (fun input => decode input (d i)) ≠ some (memory (d i))) ↔
    ¬ ∃ i, ∀ a,
      (extract realState actual i).bind (fun input => decode input a) = some (actual a) := by
  have sameMemory : memory = actual := funext sameWord
  subst realState actual
  simpa using terminal_directory_iff 0 n (fun _ => true)
    (fun i a => (extract state memory i).bind (fun input => decode input a)) memory

/-- A full affordable window has a truthful least-width cut as soon as only
    failures at widths at most `budget / window.length` are monitored. No upper
    bound on the width of any other state in the window is needed. -/
theorem small_window_minimum {Time : Type} (width : Time → Nat) (truthful : Time → Prop)
    (window : List Time) (pick : Time) (budget : Nat) (nonempty : 0 < window.length)
    (inside : pick ∈ window) (least : ∀ t ∈ window, width pick ≤ width t)
    (affordable : (window.map fun t => 1 + width t).sum ≤ budget)
    (goodSmall : ∀ t ∈ window, width t ≤ budget / window.length → truthful t) :
    1 + width pick ≤ budget / window.length ∧ truthful pick := by
  have lower (xs : List Time) (h : ∀ t ∈ xs, width pick ≤ width t) :
      (1 + width pick) * xs.length ≤ (xs.map fun t => 1 + width t).sum := by
    induction xs with
    | nil => simp
    | cons t ts ih =>
      have head := h t (by simp)
      have tail := ih (fun x hx => h x (by simp [hx]))
      simp only [List.length_cons, Nat.mul_succ, List.map_cons, List.sum_cons]
      omega
  have cap := (Nat.le_div_iff_mul_le nonempty).2 (Nat.le_trans (lower window least) affordable)
  exact ⟨cap, goodSmall pick inside (by omega)⟩

end AdvertisedSnapshotOffers
