import Std

/-! The disjoint-block lemma used for lower bounds on affine restrictions of
shared memory reads. Each block comprises independent discrepancy bits.
An arbitrary set of c linear equations collects one c-bit syndrome per block. -/
namespace SharedReadAffineBlocks

private theorem subset_length (s t : List Nat) (nd : s.Nodup)
    (sub : ∀ x ∈ s, x ∈ t) : s.length ≤ t.length := by
  induction s generalizing t with
  | nil => simp
  | cons x s ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp nd
    have xt := sub x (by simp)
    have pos := List.length_pos_of_mem xt
    have h := ih (t.erase x) tail (by
      intro y hy
      have ne : y ≠ x := fun eq => fresh (eq ▸ hy)
      exact (List.mem_erase_of_ne ne).mpr (sub y (by simp [hy])))
    rw [List.length_erase_of_mem xt] at h
    simp; omega

/-- A word-valued linear syndrome with fewer output bits has a nonzero kernel. -/
theorem kernel {d c : Nat} (small : c < d) (f : BitVec d → BitVec c)
    (lin : ∀ a b, f (a ^^^ b) = f a ^^^ f b) :
    ∃ u, u ≠ 0 ∧ f u = 0 := by
  classical
  apply Classical.byContradiction
  intro h
  have inj {a b} (same : f a = f b) : a = b := by
    apply BitVec.xor_eq_zero_iff.mp
    apply Classical.byContradiction
    intro ne
    exact h ⟨_,ne,by rw [lin,same,BitVec.xor_self]; rfl⟩
  let g (v : Nat) := (f (BitVec.ofNat d v)).toNat
  have nd : ((List.range (2^d)).map g).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ List.nodup_range
    intro a b ha hb ne eq
    apply ne
    have wordeq := @inj (BitVec.ofNat d a) (BitVec.ofNat d b)
      (BitVec.toFin_inj.mp (Fin.ext eq))
    have n := congrArg BitVec.toNat wordeq
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (List.mem_range.mp ha),
      Nat.mod_eq_of_lt (List.mem_range.mp hb)] using n
  have sub : ∀ x ∈ (List.range (2^d)).map g, x ∈ List.range (2^c) := by
    intro x hx
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (BitVec.isLt _)
  have bound := subset_length _ _ nd sub
  simp only [List.length_map,List.length_range] at bound
  exact (Nat.not_le_of_gt (Nat.pow_lt_pow_of_lt (a := 2) (by decide) small)) bound

structure Block (d c : Nat) where
  original : BitVec d
  target : BitVec d
  f : BitVec d → BitVec c
  lin : ∀ a b, f (a ^^^ b) = f a ^^^ f b

def originalSum : List (Block d c) → BitVec c
  | [] => 0
  | b :: bs => b.f b.original ^^^ originalSum bs

/-- Existence of a choice avoiding every prescribed target, with given joint syndrome. -/
def Avoids : List (Block d c) → BitVec c → Prop
  | [], s => s = 0
  | b :: bs, s => ∃ v t, v ≠ b.target ∧ Avoids bs t ∧ s = b.f v ^^^ t

theorem disjoint_blocks (small : c < d) (bs : List (Block d c)) :
    Avoids bs (originalSum bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    by_cases same : b.original = b.target
    · obtain ⟨u,ne,hu⟩ := kernel small b.f b.lin
      refine ⟨u ^^^ b.original, _, ?_, ih, ?_⟩
      · intro eq
        have e : u ^^^ b.original = (0 : BitVec d) ^^^ b.original := by
          simpa [same] using eq
        exact ne ((BitVec.xor_left_inj _).mp e)
      · simp [originalSum,b.lin,hu]
    · exact ⟨_,_,same,ih,rfl⟩

/-- Rewriting a seed address using affine feedback from the claimed earlier
replies is a bijection even off the valid graph. -/
def shear (f : BitVec y → BitVec a) (z : BitVec a × BitVec y) :=
  (z.1 ^^^ f z.2, z.2)

theorem unshear (f : BitVec y → BitVec a) (z : BitVec a × BitVec y) :
    shear f (shear f z) = z := by
  simp [shear,BitVec.xor_assoc]

def ternary (u v w : BitVec a × BitVec y) :=
  (u.1 ^^^ v.1 ^^^ w.1,u.2 ^^^ v.2 ^^^ w.2)

/-- A pure address translation that occurs at one table occurs at every
other lifted point, with exactly the same reply difference. -/
theorem transport {E : BitVec a × BitVec t → Prop}
    (closed : ∀ x y z, E x → E y → E z → E (ternary x y z))
    (f : BitVec a × BitVec t → BitVec b)
    (aff : ∀ x y z, E x → E y → E z →
      f (ternary x y z) = f x ^^^ f y ^^^ f z)
    (s v x : BitVec a) (base other : BitVec t)
    (h0 : E (s,base)) (h1 : E (s ^^^ v,base)) (h2 : E (x,other)) :
    E (v ^^^ x,other) ∧ f (v ^^^ x,other) = f (s,base) ^^^ f (s ^^^ v,base) ^^^ f (x,other) := by
  have id : ternary (s,base) (s ^^^ v,base) (x,other) = (v ^^^ x,other) := by
    simp only [ternary,Prod.mk.injEq]
    constructor
    · rw [← BitVec.xor_assoc,BitVec.xor_self,BitVec.zero_xor]
    · simp
  exact ⟨id ▸ closed _ _ _ h0 h1 h2,id ▸ aff _ _ _ h0 h1 h2⟩

theorem shear_affine (f : BitVec y → BitVec a)
    (aff : ∀ x y z, f (x ^^^ y ^^^ z) = f x ^^^ f y ^^^ f z)
    (u v w : BitVec a × BitVec y) :
    shear f (ternary u v w) = ternary (shear f u) (shear f v) (shear f w) := by
  simp only [shear,ternary,aff,Prod.mk.injEq,and_true]
  ac_rfl

end SharedReadAffineBlocks
