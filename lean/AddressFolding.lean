import Std

namespace AddressFolding

/-- Each actual read records its address, the preceding write token in its
    physical cell, and the required virtual word. -/
structure Observation (Address Token Word : Type) where
  reader : Address
  token : Token
  word : Word

theorem token_decoder_iff {Address Token Word : Type} (fallback : Word)
    (occurs : Observation Address Token Word → Prop) :
    (∃ decode : Address → Token → Word, ∀ e, occurs e → decode e.reader e.token = e.word) ↔
    (∀ e f, occurs e → occurs f → e.reader = f.reader → e.token = f.token → e.word = f.word) := by
  classical
  constructor
  · rintro ⟨decode, correct⟩ e f he hf hr ht
    rw [← correct e he, ← correct f hf, hr, ht]
  · intro unique
    let possible := fun a t (w : Word) => occurs ⟨a,t,w⟩
    let decode := fun a t =>
      if h : ∃ w, possible a t w then Classical.choose h else fallback
    refine ⟨decode, ?_⟩
    intro e he
    rcases e with ⟨a,t,w⟩
    have witness : ∃ v, possible a t v := ⟨w, he⟩
    have observed := Classical.choose_spec witness
    simpa [decode, witness] using
      unique ⟨a,t,Classical.choose witness⟩ ⟨a,t,w⟩ observed he rfl rfl

def errors (phases : List Phase) (truth guess : Phase → Bool) : Nat :=
  phases.countP (fun phase => truth phase != guess phase)

/-- Only four different phase sequences can be decoded from one source bit. -/
theorem lane_reader_bound (phases : List Phase) (truth source : Phase → Bool)
    (decode : Bool → Bool) (d : Nat)
    (zero : d ≤ errors phases truth (fun _ => false))
    (one : d ≤ errors phases truth (fun _ => true))
    (same : d ≤ errors phases truth source)
    (flip : d ≤ errors phases truth (fun p => !(source p))) :
    d ≤ errors phases truth (fun p => decode (source p)) := by
  have cases_four : (∀ b, decode b = false) ∨ (∀ b, decode b = true) ∨
      (∀ b, decode b = b) ∨ (∀ b, decode b = !b) := by
    cases l : decode false <;> cases r : decode true
    · exact Or.inl (by intro b; cases b <;> assumption)
    · exact Or.inr (Or.inr (Or.inl (by intro b; cases b <;> assumption)))
    · exact Or.inr (Or.inr (Or.inr (by intro b; cases b <;> assumption)))
    · exact Or.inr (Or.inl (by intro b; cases b <;> assumption))
  obtain h | h | h | h := cases_four
  · simpa only [h] using zero
  · simpa only [h] using one
  · simpa only [h] using same
  · simpa only [h] using flip

theorem total_errors (addresses : List Address) (nonrepresentative : Address → Bool)
    (mistakes : Address → Nat) (d : Nat)
    (individual : ∀ a ∈ addresses, nonrepresentative a = true → d ≤ mistakes a) :
    d * addresses.countP nonrepresentative ≤ (addresses.map mistakes).sum := by
  induction addresses with
  | nil => simp
  | cons a rest ih =>
    have tail := ih (fun x hx => individual x (by simp [hx]))
    simp only [List.countP_cons, List.map_cons, List.sum_cons, Nat.mul_add]
    by_cases h : nonrepresentative a = true
    · have head := individual a (by simp) h
      simp [h]
      omega
    · simp [h]
      omega

end AddressFolding
