import Std

namespace PublicChecksumPredictions

/-- Row signs when a uniformly chosen basis coefficient ranges over 0 and 1. -/
def signedTotal : List Bool → Int
  | [] => 1
  | b :: bs => signedTotal bs + (if b then -(signedTotal bs) else signedTotal bs)

theorem vanishes (bs : List Bool) (h : true ∈ bs) : signedTotal bs = 0 := by
  induction bs with
  | nil => simp at h
  | cons b bs ih =>
    cases b with
    | true => simp [signedTotal] <;> omega
    | false =>
      have hr : true ∈ bs := by simpa using h
      simp [signedTotal, ih hr]

theorem constantWhenAnnihilated (bs : List Bool) (h : true ∉ bs) :
    signedTotal bs = (2 : Int)^bs.length := by
  induction bs with
  | nil => simp [signedTotal]
  | cons b bs ih =>
    cases b with
    | true => simp at h
    | false =>
      have hr : true ∉ bs := by simpa using h
      simp [signedTotal, ih hr, Int.pow_succ] <;> omega

end PublicChecksumPredictions
