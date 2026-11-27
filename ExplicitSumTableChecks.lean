import Std

namespace ExplicitSumTableChecks

theorem unique_sum_parent {a b other guess : BitVec width}
    (one : a + other = guess) (two : b + other = guess) : a = b := by
  calc
    a = a + other - other := (BitVec.add_sub_cancel a other).symm
    _ = b + other - other := by rw [one, two]
    _ = b := BitVec.add_sub_cancel b other

def avoid [BEq α] (pool : List α) : List α → List α
  | [] => pool
  | head :: tail => avoid (pool.erase head) tail

theorem cardinal_loss [BEq α] [LawfulBEq α] (pool excluded : List α) :
    pool.length ≤ (avoid pool excluded).length + excluded.length := by
  induction excluded generalizing pool with
  | nil => simp [avoid]
  | cons head tail ih =>
    have localLoss := List.le_length_erase (l := pool) (a := head)
    have later := ih (pool.erase head)
    simp only [avoid, List.length_cons]
    omega

theorem light_fiber [BEq α] [LawfulBEq α] (pool excluded : List α)
    (light : 2 * excluded.length < pool.length) :
    pool.length < 2 * (avoid pool excluded).length := by
  have loss := cardinal_loss pool excluded
  omega

end ExplicitSumTableChecks
