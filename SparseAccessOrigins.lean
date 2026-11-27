/-! Exact provenance under arbitrary parent-port choices. -/
namespace SparseAccessOrigins

structure AddressLayer (A B : Type) where
  port : B → Nat
  pred : B → Nat → A

def copyAlong {A B W : Type} (l : AddressLayer A B) (read : A → W) : B → W :=
  fun i => read (l.pred i (l.port i))

theorem copy_eq_origin {A B V W : Type} (l : AddressLayer A B) (get : V → W)
    (origin : A → V) (data : A → W) (trueData : ∀ a, data a = get (origin a))
    (b : B) : copyAlong l data b = get (copyAlong l origin b) :=
  trueData _

inductive Route (A : Type) : Type → Type 1
  | start : Route A A
  | step {X : Type} (rest : Route A X) {Y : Type} (l : AddressLayer X Y) : Route A Y

def lookup {A W : Type} (data : A → W) {B : Type} : Route A B → B → W
  | .start => data
  | .step prev layer => copyAlong layer (lookup data prev)

theorem value_at_origin {A B W : Type} (data : A → W) (r : Route A B) (b : B) :
    lookup data r b = data (lookup id r b) := by
  induction r with
  | start => rfl
  | step prev layer ih => exact ih _

end SparseAccessOrigins
