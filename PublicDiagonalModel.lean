import Std

namespace PublicDiagonalModel

variable {Key Header Model Seed : Type}

/-- Fixing a model of the diagonal turns the query-side clauses into an equality test. -/
theorem query_iff_eq
    (hdr : Key → Header) (database : Key → Model → Prop)
    (query : Header → Key → Model → Prop)
    (sound : ∀ a x σ, database a σ → query (hdr a) x σ → x = a)
    (a : Key) (σ : Model) (left : database a σ) (right : query (hdr a) a σ)
    (x : Key) : query (hdr a) x σ ↔ x = a := by
  constructor
  · exact sound a x σ left
  · rintro rfl
    exact right

/-- The pair of public layout and seed identifies the database. -/
theorem seed_header_injective
    (hdr : Key → Header) (database : Key → Model → Prop)
    (query : Header → Key → Model → Prop)
    (sound : ∀ a x σ, database a σ → query (hdr a) x σ → x = a)
    (model : Seed → Model) (chosen : Key → Seed)
    (diagonal : ∀ a, database a (model (chosen a)) ∧ query (hdr a) a (model (chosen a)))
    (a b : Key) (same : (hdr a, chosen a) = (hdr b, chosen b)) : a = b := by
  have heads : hdr a = hdr b := congrArg Prod.fst same
  have seeds : chosen a = chosen b := congrArg Prod.snd same
  apply sound b a (model (chosen b)) (diagonal b).1
  rw [← heads, ← seeds]
  exact (diagonal a).2

end PublicDiagonalModel

#print axioms PublicDiagonalModel.query_iff_eq
#print axioms PublicDiagonalModel.seed_header_injective
