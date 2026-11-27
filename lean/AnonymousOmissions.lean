import Std

namespace AnonymousOmissions

abbrev Digit := Bool × Bool

def signAt (s x : Digit) : Int :=
  if (s.1 ^^ x.1) && (s.2 ^^ x.2) then -1 else 1

def sum4 (f : Digit → Int) : Int :=
  f (false,false) + f (false,true) + f (true,false) + f (true,true)

theorem localGram (a b : Digit) :
    sum4 (fun x => signAt a x * signAt b x) = if a = b then 4 else 0 := by
  obtain ⟨a₁,a₂⟩ := a
  obtain ⟨b₁,b₂⟩ := b
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> decide

theorem localSum (a : Digit) : sum4 (signAt a) = 2 := by
  obtain ⟨a₁,a₂⟩ := a
  cases a₁ <;> cases a₂ <;> decide

theorem sum4Scale (f : Digit → Int) (k : Int) :
    sum4 (fun x => f x * k) = sum4 f * k := by
  simp [sum4, Int.add_mul]

/-- Sum over each input digit, accumulating the product of translated signs. -/
def gram : List (Digit × Digit) → Int
  | [] => 1
  | (a,b) :: xs => sum4 fun x => signAt a x * signAt b x * gram xs

def diagonal : List (Digit × Digit) → Bool
  | [] => true
  | (a,b) :: xs => decide (a = b) && diagonal xs

theorem rowOrthogonality (pairs : List (Digit × Digit)) :
    gram pairs = if diagonal pairs then (4:Int)^pairs.length else 0 := by
  induction pairs with
  | nil => rfl
  | cons ab xs ih =>
    obtain ⟨a,b⟩ := ab
    change sum4 (fun x => (signAt a x * signAt b x) * gram xs) = _
    rw [sum4Scale, localGram, ih]
    by_cases hab : a=b <;> cases hr : diagonal xs <;>
      simp [diagonal, hab, hr, Int.pow_succ, Int.mul_comm]

/-- Total sign in one translated row. -/
def rowTotal : List Digit → Int
  | [] => 1
  | a :: xs => sum4 fun x => signAt a x * rowTotal xs

theorem translatedBias (shifts : List Digit) : rowTotal shifts = (2:Int)^shifts.length := by
  induction shifts with
  | nil => rfl
  | cons a xs ih =>
    change sum4 (fun x => signAt a x * rowTotal xs) = _
    rw [sum4Scale, localSum, ih]
    simp [Int.pow_succ, Int.mul_comm]

end AnonymousOmissions
