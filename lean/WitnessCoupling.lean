import Std

namespace WitnessCoupling

/-- Count events on a finite sample space, allowing repeated points. -/
def countTrue {α : Type} (f : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => (f x).toNat + countTrue f xs

theorem count_le_add_event {α : Type} (p q bad : α → Bool)
    (coupled : ∀ x, bad x = false → p x = q x) (points : List α) :
    countTrue p points ≤ countTrue q points + countTrue bad points := by
  induction points with
  | nil => simp [countTrue]
  | cons x xs ih =>
    have point : (p x).toNat ≤ (q x).toNat + (bad x).toNat := by
      cases e : bad x with
      | false => simp [coupled x e, e]
      | true => cases p x <;> cases q x <;> decide
    simp only [countTrue]
    omega

/-- The witnesses and countermoves may differ across inputs. A common bound
    on all pure-pair scores controls the difference between their guarantees. -/
theorem game_discrepancy {Left Right : Type} (a b : Left → Right → Nat)
    (high low loss : Nat) (yes : ∃ l, ∀ r, high ≤ a l r)
    (no : ∀ l, ∃ r, b l r ≤ low)
    (bound : ∀ l r, a l r ≤ b l r + loss) : high ≤ low + loss := by
  obtain ⟨l, win⟩ := yes
  obtain ⟨r, stop⟩ := no l
  have hi := win r
  have diff := bound l r
  omega

end WitnessCoupling
