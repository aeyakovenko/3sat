import Std

namespace QuadraticStoreTarget

def hitBits (a b c u : Bool) : Bool :=
  !(xor u (a && b)) && !(u && c)

theorem hit_iff (a b c u : Bool) :
    hitBits a b c u = true ↔ u = (a && b) ∧ (a && b && c) = false := by
  cases a <;> cases b <;> cases c <;> cases u <;> decide

theorem zero_address_iff (a b c u : α → Bool) :
    (∀ j, hitBits (a j) (b j) (c j) (u j) = true) ↔
    u = (fun j => a j && b j) ∧ (∀ j, (a j && b j && c j) = false) := by
  constructor
  · intro h
    exact ⟨funext (fun j => ((hit_iff ..).mp (h j)).1),
      fun j => ((hit_iff ..).mp (h j)).2⟩
  · rintro ⟨rfl,h⟩ j
    exact (hit_iff ..).mpr ⟨rfl, h j⟩

theorem exists_unique_aux (a b c : α → Bool) :
    (∃ u : α → Bool, (∀ j, hitBits (a j) (b j) (c j) (u j) = true) ∧
      ∀ v : α → Bool, (∀ j, hitBits (a j) (b j) (c j) (v j) = true) → v = u) ↔
    ∀ j, (a j && b j && c j) = false := by
  constructor
  · rintro ⟨u,h,_⟩
    exact ((zero_address_iff ..).mp h).2
  · intro h
    exact ⟨fun j => a j && b j, (zero_address_iff ..).mpr ⟨rfl,h⟩,
      fun _ hv => ((zero_address_iff ..).mp hv).1⟩

#print axioms exists_unique_aux

end QuadraticStoreTarget
