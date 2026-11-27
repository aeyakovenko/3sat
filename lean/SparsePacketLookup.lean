import Std

/-! Semantic parts of the sparse packet lookup argument. The two hashes can
have arbitrary finite or infinite domains. No cardinality, hashing probability
or communication upper bound is assumed in the lookup identity. -/
namespace SparsePacketLookup

section Rectangles
variable {Bank Address : Type}
abbrev Query (Bank Address : Type) := Bank → Address
abbrev Database (Bank Address : Type) := Bank → Address → Bool

def projection (rows : Query Bank Address → Prop) (i : Bank) (a : Address) :=
  ∃ q, rows q ∧ q i = a

def allOne (rows : Query Bank Address → Prop)
    (cols : Database Bank Address → Prop) : Prop :=
  ∀ q, rows q → ∀ db, cols db → ∀ i, db i (q i) = true

theorem rectangle_iff_forced_projections
    (rows : Query Bank Address → Prop) (cols : Database Bank Address → Prop) :
    allOne rows cols ↔
      ∀ db, cols db → ∀ i a, projection rows i a → db i a = true := by
  constructor
  · rintro h db hd i a ⟨q, hq, rfl⟩
    exact h q hq db hd i
  · intro h q hq db hd i
    exact h db hd i (q i) ⟨q, hq, rfl⟩

/-- The restrictions to all unforced coordinates distinguish the columns. -/
theorem columns_determined_off_projections
    {rows : Query Bank Address → Prop} {cols : Database Bank Address → Prop}
    (hc : allOne rows cols) {x y : Database Bank Address}
    (hx : cols x) (hy : cols y)
    (hoff : ∀ i a, ¬projection rows i a → x i a = y i a) : x = y := by
  have hp := (rectangle_iff_forced_projections rows cols).mp hc
  funext i a
  by_cases h : projection rows i a
  · exact (hp x hx i a h).trans (hp y hy i a h).symm
  · exact hoff i a h

/-- Restricting each bank to its coordinate projection retains the full row. -/
def rowInProduct (rows : Query Bank Address → Prop) (q : {q // rows q}) :
    (i : Bank) → {a : Address // projection rows i a} :=
  fun i => ⟨q.val i, q.val, q.property, rfl⟩

theorem rowInProduct_injective (rows : Query Bank Address → Prop)
    {x y : {q // rows q}} (e : rowInProduct rows x = rowInProduct rows y) :
    x = y := by
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun e i)
end Rectangles

section Sparse
variable {Key Value Bucket Slot : Type}

/-- Place an occupied key in its specified slot, choosing an arbitrary
representative if the two hashes collide. -/
noncomputable def slots (live : Key → Prop) (value : Key → Value)
    (bucket : Key → Bucket) (secondary : Bucket → Key → Slot)
    (b : Bucket) (s : Slot) : Option (Key × Value) := by
  classical
  exact if h : ∃ k, live k ∧ bucket k = b ∧ secondary b k = s then
    some (Classical.choose h, value (Classical.choose h)) else none

def separated (live : Key → Prop) (bucket : Key → Bucket)
    (secondary : Bucket → Key → Slot) : Prop :=
  ∀ b k l, live k → live l → bucket k = b → bucket l = b →
    secondary b k = secondary b l → k = l

theorem occupied_lookup {live : Key → Prop} (value : Key → Value)
    {bucket : Key → Bucket} {secondary : Bucket → Key → Slot}
    (sep : separated live bucket secondary) {k : Key} (hk : live k) :
    slots live value bucket secondary (bucket k) (secondary (bucket k) k) =
      some (k, value k) := by
  classical
  have has : ∃ l, live l ∧ bucket l = bucket k ∧
      secondary (bucket k) l = secondary (bucket k) k := ⟨k, hk, rfl, rfl⟩
  have hs := Classical.choose_spec has
  have eq := sep (bucket k) (Classical.choose has) k hs.1 hk hs.2.1 rfl hs.2.2
  simp [slots, has, eq]

theorem stored_tag_is_live {live : Key → Prop} {value : Key → Value}
    {bucket : Key → Bucket} {secondary : Bucket → Key → Slot}
    {b : Bucket} {s : Slot} {k : Key} {v : Value}
    (found : slots live value bucket secondary b s = some (k, v)) :
    live k := by
  classical
  unfold slots at found
  split at found
  next h =>
    have eq : Classical.choose h = k := congrArg Prod.fst (Option.some.inj found)
    exact eq ▸ (Classical.choose_spec h).1
  next => contradiction

/-- The response includes an original-address tag. An absent key is allowed
to land in a slot occupied by an entirely different key. -/
def checked [DecidableEq Key] (default : Value) (k : Key) :
    Option (Key × Value) → Value
  | none => default
  | some (tag, v) => if tag = k then v else default

theorem sparse_lookup_eq [DecidableEq Key] (default : Value)
    {live : Key → Prop} [DecidablePred live] (value : Key → Value)
    {bucket : Key → Bucket} {secondary : Bucket → Key → Slot}
    (sep : separated live bucket secondary) (k : Key) :
    checked default k
        (slots live value bucket secondary (bucket k) (secondary (bucket k) k)) =
      if live k then value k else default := by
  by_cases hk : live k
  · rw [occupied_lookup value sep hk]
    simp [checked, hk]
  · simp only [if_neg hk]
    cases h : slots live value bucket secondary (bucket k) (secondary (bucket k) k) with
    | none => rfl
    | some pair =>
      obtain ⟨tag, v⟩ := pair
      have hl := stored_tag_is_live h
      have ne : tag ≠ k := fun e => hk (e ▸ hl)
      simp [checked, ne]
end Sparse

end SparsePacketLookup
