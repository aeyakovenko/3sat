import Std

namespace SparseInterfaceGluing

variable {Chunk Name : Type} [DecidableEq Chunk]

/-- Select one occurrence's local model. Names absent from the whole file receive false. -/
def assembled (chunks : List Chunk) (occurs : Chunk → Name → Bool)
    (models : Chunk → Name → Bool) (i : Name) : Bool :=
  match chunks with
  | [] => false
  | b :: tail => if occurs b i then models b i else assembled tail occurs models i

theorem agrees_at_occurrence (chunks : List Chunk) (occurs : Chunk → Name → Bool)
    (models : Chunk → Name → Bool) (base : Name → Bool)
    (allowed : ∀ b c i, b ≠ c → occurs b i = true → occurs c i = true → models b i = base i)
    (b : Chunk) (i : Name) (member : b ∈ chunks) (present : occurs b i = true) :
    assembled chunks occurs models i = models b i := by
  induction chunks with
  | nil => simp at member
  | cons c tail ih =>
    by_cases here : occurs c i = true
    · simp only [assembled,here,ite_true]
      by_cases same : c = b
      · simp [same]
      · exact (allowed c b i same here present).trans (allowed b c i (Ne.symm same) present here).symm
    · simp only [assembled, here, if_false]
      apply ih
      rcases List.mem_cons.mp member with top | later
      · subst c; exact False.elim (here present)
      · exact later

/-- Existential per-chunk models after the universal chunk choice are enough,
provided every disagreement with the public assignment is confined to one chunk. -/
theorem glue (chunks : List Chunk) (occurs : Chunk → Name → Bool) (models : Chunk → Name → Bool)
    (base : Name → Bool) (accept : Chunk → (Name → Bool) → Prop)
    (locality : ∀ b x y, (∀ i, occurs b i = true → x i = y i) → accept b x → accept b y)
    (satisfies : ∀ b ∈ chunks, accept b (models b))
    (allowed : ∀ b c i, b ≠ c → occurs b i = true → occurs c i = true → models b i = base i) :
    ∃ assignment, ∀ b ∈ chunks, accept b assignment := by
  refine ⟨assembled chunks occurs models, ?_⟩
  intro b member
  apply locality b (models b) _ _ (satisfies b member)
  intro i present
  exact (agrees_at_occurrence chunks occurs models base allowed b i member present).symm

end SparseInterfaceGluing

#print axioms SparseInterfaceGluing.glue
