import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Hard
import Mathlib.Algebra.Field.ZMod
open Filter OAI.LinearAlgebra.MatrixExponent
theorem binary_one_list :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ w : ℕ in atTop, ∀ m : ℕ,
      Realizes (ZMod 2) w 1 m → (listBits w : ℝ) * (w : ℝ) ^ η < m := by
  obtain ⟨η, hη, h⟩ := BatchDescent.manyList_full (ZMod 2)
  refine ⟨η, hη, ?_⟩
  filter_upwards [h] with w hw
  intro m hm
  have hpow : 1 ≤ (2 : ℝ) ^ ((w : ℝ) ^ (1 + η)) :=
    Real.one_le_rpow (by norm_num) (Real.rpow_nonneg (by positivity) _)
  simpa using hw 1 m (by decide) (by simpa using hpow) hm
#print axioms OAI.LinearAlgebra.MatrixExponent.BatchDescent.manyList_full
#print axioms binary_one_list

theorem binary_one_list_diagram :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ w : ℕ in atTop,
      ∀ G : Diagram (ZMod 2) (lists w 1) .unit,
      G.Trivalent →
      G.eval = (fun x _ => distinctPower (ZMod 2) w 1 x) →
      (listBits w : ℝ) * (w : ℝ) ^ η <
        (Fintype.card G.V + listBits w : ℕ) := by
  obtain ⟨η, hη, h⟩ := binary_one_list
  refine ⟨η, hη, ?_⟩
  filter_upwards [h] with w hw
  intro G htri heval
  apply hw (Fintype.card G.V + listBits w)
  refine ⟨Fintype.card G.V, ?_, by simp⟩
  exact heval ▸ Diagram.net G htri

#print axioms binary_one_list_diagram
