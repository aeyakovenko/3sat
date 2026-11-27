import Std

namespace BinaryProductWitnessLines

/-- These are the matrix-ring laws used below. Multiplication may be noncommutative. -/
class BinaryRing (R : Type) extends Add R, Mul R, Zero R where
  addAssoc (x y z : R) : (x+y)+z=x+(y+z)
  addComm (x y : R) : x+y=y+x
  zeroAdd (x : R) : 0+x=x
  selfAdd (x : R) : x+x=0
  mulAssoc (x y z : R) : (x*y)*z=x*(y*z)
  mulAdd (x y z : R) : x*(y+z)=x*y+x*z
  addMul (x y z : R) : (x+y)*z=x*z+y*z

variable {R : Type} [BinaryRing R]

private theorem addLeftComm (x y z : R) : x+(y+z)=y+(x+z) := by
  rw [← BinaryRing.addAssoc, BinaryRing.addComm x y, BinaryRing.addAssoc]

private theorem cancelAdd (x : R) {y z : R} (h : x+y=x+z) : y=z := by
  have h' := congrArg (fun a => x+a) h
  simpa only [← BinaryRing.addAssoc, BinaryRing.selfAdd, BinaryRing.zeroAdd] using h'

private theorem eqOfAddZero {x y : R} (h : x+y=0) : x=y := by
  exact (cancelAdd x (h.trans (BinaryRing.selfAdd x).symm)).symm

def delta (A B a b : R) := A*b + a*B + a*b

private theorem increment (A B a b : R) :
    (A+a)*(B+b)=A*B+delta A B a b := by
  simp only [delta, BinaryRing.mulAdd, BinaryRing.addMul, BinaryRing.addAssoc,
    BinaryRing.addComm, addLeftComm]

/-- The same triple direction `(a,b,c)` is legal at two product points whose
    input factors differ by `(X,Y)`. This forces the indicated polar identity. -/
theorem twoOrigins (A B X Y a b c : R)
    (h₀ : A*B+c=(A+a)*(B+b))
    (h₁ : (A+X)*(B+Y)+c=((A+X)+a)*((B+Y)+b)) : X*b = a*Y := by
  rw [increment A B a b] at h₀
  rw [increment (A+X) (B+Y) a b] at h₁
  have he := (cancelAdd (A*B) h₀).symm.trans (cancelAdd ((A+X)*(B+Y)) h₁)
  have hexp : delta (A+X) (B+Y) a b = delta A B a b + (X*b+a*Y) := by
    simp only [delta, BinaryRing.addMul, BinaryRing.mulAdd, BinaryRing.addAssoc,
      BinaryRing.addComm, addLeftComm]
  rw [hexp] at he
  have hadd : delta A B a b + 0 = delta A B a b := by
    rw [BinaryRing.addComm, BinaryRing.zeroAdd]
  exact eqOfAddZero (cancelAdd (delta A B a b) (hadd.trans he)).symm

/-- Two graph directions in a flat satisfy the symmetric mixed product identity. -/
theorem flatPolar (A B a b a' b' c c' : R)
    (ha : A*B+c=(A+a)*(B+b)) (hb : A*B+c'=(A+a')*(B+b'))
    (hab : (A*B+c)+c'=((A+a)+a')*((B+b)+b')) : a*b'=a'*b := by
  exact twoOrigins A B a b a' b' c' hb (ha ▸ hab)

/-- Replace the factor differences by invertible completions on the directions
    which annihilate the two perturbations. -/
theorem completedPolar {X Y X' Y' a b : R}
    (h : X*b=a*Y) (hx : X'*b=X*b) (hy : a*Y=a*Y') : X'*b=a*Y' :=
  hx.trans (h.trans hy)

/-- Left and right cancellation by the completed matrices is sufficient.
    Normalized directions `u` and `v` then commute. -/
theorem normalizedCommute (X Y u v : R) (cancelX : ∀ i j : R, X*i=X*j → i=j)
    (cancelY : ∀ i j : R, i*Y=j*Y → i=j)
    (h : (X*u)*(v*Y)=(X*v)*(u*Y)) : u*v=v*u := by
  apply cancelY
  apply cancelX
  simpa only [BinaryRing.mulAssoc] using h

/-- Given `a=X*u` and `a'=X*v`, existence of which follows from invertibility
    of `X`, the two-origin equations supply the corresponding B-coordinates. -/
theorem normalizeDirections (X Y a b a' b' u v : R)
    (cancelX : ∀ i j : R, X*i=X*j → i=j) (cancelY : ∀ i j : R, i*Y=j*Y → i=j)
    (hu : a=X*u) (hv : a'=X*v) (huY : X*b=a*Y) (hvY : X*b'=a'*Y)
    (polar : a*b'=a'*b) : b=u*Y ∧ b'=v*Y ∧ u*v=v*u := by
  have h₁ : b=u*Y := cancelX _ _ (by simpa only [hu, BinaryRing.mulAssoc] using huY)
  have h₂ : b'=v*Y := cancelX _ _ (by simpa only [hv, BinaryRing.mulAssoc] using hvY)
  exact ⟨h₁, h₂, normalizedCommute X Y u v cancelX cancelY
    (by simpa only [hu, hv, h₁, h₂] using polar)⟩

end BinaryProductWitnessLines
