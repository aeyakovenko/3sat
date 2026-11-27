import Std

namespace AdaptiveMarkedRead

/-- The value stored at a previously written address is a public function of
    the destination. An unmodified cell still holds its initial content. -/
structure Memory (α : Type) where
  initial : α → α
  marked : α → Bool
  payload : α → α

def read (m : Memory α) (a : α) : α :=
  if m.marked a then m.payload a else m.initial a

/-- In the crossed schedule the selected address is the old word and the
    compulsory payload is f of that address. -/
theorem crossed_next (initial f : α → α) (marks : α → Bool) (p : α) :
    f (read ⟨initial, marks, f⟩ p) =
      (if marks p then f (f p) else f (initial p)) := by
  simp only [read]
  cases marks p <;> rfl

/-- A splice keeps original memory from the second run off the prefix's read
    set. On the read set only previously read but unmarked cells need cached
    original data. Marked cells may occur outside the read set as well. -/
theorem splice_read (left right payload : α → α) (seen marked : α → Bool)
    (cached : ∀ i, seen i = true → marked i = false → left i = right i)
    (p : α) :
    read ⟨fun i => if seen i then left i else right i, marked, payload⟩ p =
      read ⟨right, marked, payload⟩ p := by
  cases hm : marked p <;> cases hs : seen p <;> simp [read, hm, hs, cached p]

/-- The current unmarked address is a terminal point of any completed
    episode in which it appears, if every nonterminal point was already
    marked and marks are monotone. -/
theorem unmarked_occurrence_is_terminal {holds : α → Prop} {xs : List α} {a z : α}
    (oldMarks : ∀ x ∈ xs, holds x) (unmarked : ¬ holds a)
    (occurs : a ∈ xs ++ [z]) : a = z := by
  simp only [List.mem_append, List.mem_singleton] at occurs
  rcases occurs with older | endPoint
  · exact False.elim (unmarked (oldMarks a older))
  · exact endPoint

end AdaptiveMarkedRead
