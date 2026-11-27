import Std

namespace StreamFilter

/-- Most positions in a stream are unrelated to the selected edge and offset. -/
def saw (target : Bool) : Bool → List (Option Bool) → Bool
  | seen, [] => seen
  | seen, event :: rest => saw target (seen || decide (event = some target)) rest

theorem saw_iff (bit : Bool) (events : List (Option Bool)) (initial : Bool) :
    saw bit initial events = true ↔ initial = true ∨ some bit ∈ events := by
  induction events generalizing initial with
  | nil => simp [saw]
  | cons head rest ih =>
    simp only [saw, ih, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, or_assoc]
    rw [show (head = some bit ↔ some bit = head) from eq_comm]

def mismatch (events : List (Option Bool)) : Prop :=
  saw false false events = true ∧ saw true false events = true

theorem monitor_two_endpoints {events : List (Option Bool)} (a b : Bool)
    (endpoints : ∀ c, some c ∈ events ↔ c = a ∨ c = b) :
    mismatch events ↔ a ≠ b := by
  cases a <;> cases b <;> simp [mismatch, saw_iff, endpoints]

/-- Both searches intersect the very same locally accepted stream language. -/
theorem filter_test {Stream Slot : Type} (localOK accepts : Stream → Prop)
    (bad : Stream → Slot → Prop) :
    ((∃ s, localOK s ∧ accepts s) ∧
      ¬ ∃ s i, localOK s ∧ accepts s ∧ bad s i) ↔
    ((∃ s, localOK s ∧ accepts s) ∧
      ∀ s, localOK s → accepts s → ∀ i, ¬ bad s i) := by
  constructor
  · rintro ⟨inhabited, safe⟩
    exact ⟨inhabited, fun s hs hf i hi => safe ⟨s, i, hs, hf, hi⟩⟩
  · rintro ⟨inhabited, safe⟩
    refine ⟨inhabited, ?_⟩
    rintro ⟨s, i, hs, hf, hi⟩
    exact safe s hs hf i hi

end StreamFilter
