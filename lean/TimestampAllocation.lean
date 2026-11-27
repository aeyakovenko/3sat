import Std

namespace TimestampAllocation

structure Cell where
  start : Nat
  level : Nat
  deriving Repr

def stop (c : Cell) : Nat := c.start + 2 ^ c.level

/-- Cover the first n positions of a block whose length is 2^h. -/
def pieces : Nat → Nat → Nat → List Cell
  | 0, b, n => if n = 0 then [] else [⟨b, 0⟩]
  | h+1, b, n =>
    if n = 2^(h+1) then [⟨b,h+1⟩]
    else if n ≤ 2^h then pieces h b n
    else ⟨b,h⟩ :: pieces h (b+2^h) (n-2^h)

/-- A partial block needs only one dyadic piece per level, up to endpoints. -/
theorem piecesLength (h b n : Nat) :
    (pieces h b n).length ≤ h+1 := by
  induction h generalizing b n with
  | zero => by_cases hz : n = 0 <;> simp [pieces, hz]
  | succ h ih =>
    simp only [pieces]
    split
    · simp
    · split
      · have := ih b n
        omega
      · simp only [List.length_cons]
        have := ih (b+2^h) (n-2^h)
        omega

/-- Every admitted index is covered by an aligned piece with an admissible
right endpoint. The row itself need never know where the prefix ends. -/
theorem covers (h b n j : Nat) (aligned : 2^h ∣ b) (fits : n ≤ 2^h)
    (left : b ≤ j) (right : j < b+n) :
    ∃ c ∈ pieces h b n, c.level ≤ h ∧ 2^c.level ∣ c.start ∧
      c.start ≤ j ∧ j < stop c ∧ stop c ≤ b+n := by
  induction h generalizing b n j with
  | zero =>
    have one : n = 1 := by simp at fits; omega
    subst n
    exact ⟨⟨b,0⟩, by simp [pieces], by simp [stop]; omega⟩
  | succ h ih =>
    have sumPow : 2^(h+1) = 2^h + 2^h := by simp [Nat.pow_succ, Nat.mul_two]
    have halfDiv : 2^h ∣ 2^(h+1) := ⟨2, Nat.pow_succ 2 h⟩
    have smaller : 2^h ∣ b := Nat.dvd_trans halfDiv aligned
    by_cases full : n = 2^(h+1)
    · subst n
      exact ⟨⟨b,h+1⟩, by simp [pieces], Nat.le_refl _, aligned, left, right, Nat.le_refl _⟩
    by_cases half : n ≤ 2^h
    · obtain ⟨c,hc,hl,ha,hj⟩ := ih b n j smaller half left right
      exact ⟨c, by simpa [pieces, full, half] using hc, by omega, ha, hj⟩
    by_cases earlier : j < b+2^h
    · exact ⟨⟨b,h⟩, by simp [pieces, full, half], by simp [stop]; omega⟩
    · have nextAligned : 2^h ∣ b+2^h := Nat.dvd_add smaller (Nat.dvd_refl _)
      obtain ⟨c,hc,hl,ha,hj1,hj2,hend⟩ :=
        ih (b+2^h) (n-2^h) j nextAligned (by omega) (by omega) (by omega)
      exact ⟨c, by simp [pieces, full, half, hc], by omega, ha, hj1, hj2, by omega⟩

end TimestampAllocation
