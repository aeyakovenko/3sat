import Std

namespace ProductWindowDefects

/-- A finite observation can be written as a partial function. Duplicate entries
in an implementation are checked for agreement before forming this function. -/
def agreesWith {Key Value : Type} (full : Key → Value) (partialMap : Key → Option Value) : Prop :=
  ∀ k v, partialMap k = some v → full k = v

theorem product_completion {Key Value : Type} (domain : Key → Value → Prop)
    (defaultValue : Key → Value) (hdefault : ∀ k, domain k (defaultValue k))
    (partialMap : Key → Option Value)
    (hallowed : ∀ k v, partialMap k = some v → domain k v) :
    ∃ full, agreesWith full partialMap ∧ ∀ k, domain k (full k) := by
  let full := fun k => (partialMap k).getD (defaultValue k)
  refine ⟨full, ?_, ?_⟩
  · intro k v hv
    simp [full, hv]
  · intro k
    cases h : partialMap k with
    | none => simpa [full, h] using hdefault k
    | some v => simpa [full, h] using hallowed k v h

/-- Normalize each address's stored value to its class label and decode it back. -/
theorem alias_completion {Addr Key Value : Type} (key : Addr → Key)
    (encode decode : Addr → Value → Value) (roundTrip : ∀ a v, decode a (encode a v) = v)
    (domain : Key → Value → Prop) (defaultValue : Key → Value)
    (hdefault : ∀ k, domain k (defaultValue k))
    (observed : Addr → Option Value) (labels : Key → Option Value)
    (hlabels : ∀ a v, observed a = some v → labels (key a) = some (encode a v))
    (hallowed : ∀ k v, labels k = some v → domain k v) :
    ∃ classValue : Key → Value, (∀ k, domain k (classValue k)) ∧
      agreesWith (fun a => decode a (classValue (key a))) observed := by
  obtain ⟨classValue, agrees, admissible⟩ :=
    product_completion domain defaultValue hdefault labels hallowed
  refine ⟨classValue, admissible, ?_⟩
  intro a v hv
  change decode a (classValue (key a)) = v
  rw [agrees (key a) (encode a v) (hlabels a v hv), roundTrip]

/-- Membership of an alias row can fail at one address or at two addresses.
For each address, values stored in this theorem are already normalized. -/
theorem alias_iff_unary_and_pair {Addr Key Value : Type} (key : Addr → Key)
    (bits : Addr → Value) (domain : Key → Value → Prop)
    (defaultValue : Key → Value) (hdefault : ∀ k, domain k (defaultValue k)) :
    (∃ labels : Key → Value, (∀ k, domain k (labels k)) ∧ ∀ a, labels (key a) = bits a) ↔
    (∀ a, domain (key a) (bits a)) ∧ ∀ a b, key a = key b → bits a = bits b := by
  classical
  constructor
  · rintro ⟨labels, allowed, agrees⟩
    constructor
    · intro a
      rw [← agrees a]
      exact allowed (key a)
    · intro a b eq
      rw [← agrees a, ← agrees b, eq]
  · rintro ⟨allowed, compatible⟩
    let labels := fun k => if h : ∃ a, key a = k then bits h.choose else defaultValue k
    refine ⟨labels, ?_, ?_⟩
    · intro k
      simp only [labels]
      split
      next h =>
        exact Eq.mp (congrArg (fun j => domain j (bits h.choose)) h.choose_spec) (allowed h.choose)
      next => exact hdefault k
    · intro a
      have hex : ∃ b, key b = key a := ⟨a, rfl⟩
      simp only [labels, dif_pos hex]
      exact compatible _ _ hex.choose_spec

/-- If the local checks cover each step, they cover any interval. -/
def iterate {S : Type} (step : S → S) : Nat → S → S
  | 0, s => s
  | n+1, s => step (iterate step n s)

theorem invariant_interval {S : Type} (step : S → S) (family : Nat → S → Prop)
    (closed : ∀ t s, family t s → family (t+1) (step s))
    (start width : Nat) (s : S) (hs : family start s) :
    family (start+width) (iterate step width s) := by
  induction width with
  | zero => exact hs
  | succ n ih => exact closed (start+n) _ ih

/-- A sound product over two banks that must agree on all choices pins each projection. -/
theorem equality_pins_product {Value : Type} (left right : Value → Prop)
    (actual : Value) (ha : left actual) (hb : right actual)
    (agree : ∀ x y, left x → right y → x = y) :
    (∀ x, left x ↔ x = actual) ∧ (∀ x, right x ↔ x = actual) := by
  constructor
  · intro x
    constructor
    · intro hx
      exact agree x actual hx hb
    · rintro rfl
      exact ha
  · intro x
    constructor
    · intro hx
      exact (agree actual x ha hx).symm
    · rintro rfl
      exact hb

end ProductWindowDefects
