import Std

namespace ResidueHeaders

/-- The available header lengths span all residues, regardless of the payload. -/
theorem matchingHeader (payload output modulus : Nat) (positive : 0 < modulus) :
    ∃ length, 0 < length ∧ length ≤ modulus ∧
      (payload + length) % modulus = output % modulus := by
  have p := Nat.mod_lt payload positive
  have o := Nat.mod_lt output positive
  by_cases order : payload % modulus < output % modulus
  · let length := output % modulus - payload % modulus
    have hit : payload % modulus + length = output % modulus := by
      dsimp [length]
      omega
    refine ⟨length, by dsimp [length]; omega, by dsimp [length]; omega, ?_⟩
    rw [← Nat.mod_add_mod payload modulus length, hit, Nat.mod_eq_of_lt o]
  · let length := modulus + output % modulus - payload % modulus
    have hit : payload % modulus + length = output % modulus + modulus := by
      dsimp [length]
      omega
    refine ⟨length, by dsimp [length]; omega, by dsimp [length]; omega, ?_⟩
    rw [← Nat.mod_add_mod payload modulus length, hit, Nat.add_mod_right,
      Nat.mod_eq_of_lt o]

/-- If every fallback has a timely residue-header companion on its own
    payload, the shortest timely name has the prescribed residue. -/
theorem shortestResidue (timely : Nat → Prop) (output modulus shortest : Nat)
    (positive : 0 < modulus) (attained : timely shortest)
    (minimal : ∀ n, timely n → shortest ≤ n)
    (branches : ∀ n, timely n → n % modulus = output % modulus ∨
      ∃ payload, n = payload + modulus + 1 ∧
        ∀ length, 0 < length → length ≤ modulus →
          (payload + length) % modulus = output % modulus →
          timely (payload + length)) :
    shortest % modulus = output % modulus := by
  rcases branches shortest attained with good | ⟨payload, tooLong, companion⟩
  · exact good
  · obtain ⟨length, nonzero, bounded, correct⟩ := matchingHeader payload output modulus positive
    have noShorter := minimal _ (companion length nonzero bounded correct)
    omega

end ResidueHeaders
