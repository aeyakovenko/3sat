import Std

namespace GraphCatalogCodeCount

/-- All PCs including the two terminal states; arithmetic, load, store, branch. -/
def codeBound (slots width : Nat) : Nat :=
  let pcs := slots + 2
  let operands := slots + 2 ^ width
  let data := 20 * slots * operands ^ 2 * pcs
  let load := slots * operands * pcs
  let store := operands ^ 2 * pcs
  let branch := 3 * operands ^ 2 * pcs ^ 2
  pcs * (data + load + store + branch) ^ slots

theorem sixteen_six : codeBound 6 4 < 2 ^ 120 := by decide
theorem seventeen_append :
    codeBound 6 4 * 2 ^ 16 + codeBound 6 5 < 2 ^ 136 := by decide
theorem any_sixteen_append_seven : codeBound 6 5 < 2 ^ 133 := by decide
theorem fixed_sixteen_append_eighteen : codeBound 6 6 < 2 ^ 153 := by decide

end GraphCatalogCodeCount
