import Std

namespace CompleteClauseSeed

/-- Remove the cube face of a chosen direction through the first uncovered point. -/
def search : Nat → List Nat → List Nat → Bool
  | _, _, [] => true
  | 0, _, _ :: _ => false
  | n+1, dirs, x :: xs =>
    dirs.any fun d => search n (dirs.erase d) (xs.filter fun y => y &&& d != x &&& d)

def Covers (f : Nat → Nat) (dirs xs : List Nat) : Prop :=
  ∀ a ∈ xs, ∃ d ∈ dirs, a &&& d = f d

theorem search_complete (f : Nat → Nat) (n : Nat) (dirs xs : List Nat)
    (hlen : dirs.length ≤ n) (h : Covers f dirs xs) : search n dirs xs = true := by
  induction n generalizing dirs xs with
  | zero =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      have hd : dirs = [] := List.length_eq_zero_iff.mp (by omega)
      obtain ⟨d, dh, _⟩ := h x (by simp)
      simp [hd] at dh
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      obtain ⟨d, dh, hx⟩ := h x (by simp)
      apply List.any_eq_true.mpr
      refine ⟨d, dh, ih _ _ ?_ ?_⟩
      · rw [List.length_erase_of_mem dh]
        omega
      · intro y hy
        obtain ⟨hmem, hne⟩ := List.mem_filter.mp hy
        obtain ⟨c, hc, heq⟩ := h y (List.mem_cons_of_mem _ hmem)
        have hcd : c ≠ d := by
          rintro rfl
          simp [heq, hx] at hne
        exact ⟨c, (List.mem_erase_of_ne hcd).mpr hc, heq⟩

def triples5 : List Nat := [7,11,19,13,21,25,14,22,26,28]

theorem uncovered_on_five (f : Nat → Nat) :
    ∃ a < 32, ∀ d ∈ triples5, a &&& d ≠ f d := by
  classical
  apply Classical.byContradiction
  intro bad
  have cov : Covers f triples5 (List.range 32) := by
    intro a ha
    apply Classical.byContradiction
    intro noFace
    apply bad
    exact ⟨a, List.mem_range.mp ha, fun d hd heq => noFace ⟨d, hd, heq⟩⟩
  have full := search_complete f 10 triples5 (List.range 32) (by decide) cov
  have empty : search 10 triples5 (List.range 32) = false := by native_decide
  rw [empty] at full
  contradiction

/-- Each pair is a support mask and its single forbidden assignment on that mask. -/
def six : List (Nat × Nat) :=
  [(7,4),(11,2),(19,16),(35,1),(13,8),(21,0),(37,1),(25,1),(41,41),(49,49),
   (14,14),(22,22),(38,38),(26,26),(42,42),(50,50),(28,28),(44,44),(52,52),(56,56)]

theorem six_covers : (List.range 64).all
    (fun a => six.any (fun p => a &&& p.1 == p.2)) = true := by native_decide



def supportsOf (n k : Nat) : List Nat :=
  (List.range (2^n)).filter fun mask =>
    ((List.range n).countP fun i => mask.testBit i) == k

def validCover (n k : Nat) (rows : List (Nat × Nat)) : Bool :=
  (rows.map Prod.fst).mergeSort (· ≤ ·) == supportsOf n k &&
  rows.all (fun p => p.2 &&& p.1 == p.2) &&
  (List.range (2^n)).all (fun a => rows.any (fun p => a &&& p.1 == p.2))

theorem five_directions : triples5.mergeSort (· ≤ ·) = supportsOf 5 3 := by native_decide
theorem six_distinct_cover : validCover 6 3 six = true := by native_decide

def sevenFour : List (Nat × Nat) :=
  [(15,0),(23,19),(39,37),(71,0),(27,17),(43,10),(75,64),(51,1),
   (83,17),(99,66),(29,29),(45,37),(77,76),(53,0),(85,81),(101,64),
   (57,33),(89,81),(105,1),(113,1),(30,10),(46,46),(78,12),(54,32),
   (86,4),(102,34),(58,34),(90,16),(106,2),(114,66),(60,32),(92,0),
   (108,100),(116,112),(120,48)]

theorem sevenFour_covers : validCover 7 4 sevenFour = true := by native_decide

def eightFive : List (Nat × Nat) :=
  [(31,0),(47,42),(79,14),(143,132),(55,53),(87,71),(151,148),(103,33),
   (167,37),(199,133),(59,18),(91,72),(155,137),(107,64),(171,40),(203,202),
   (115,115),(179,147),(211,82),(227,193),(61,9),(93,17),(157,148),(109,105),
   (173,9),(205,197),(117,16),(181,5),(213,21),(229,4),(121,64),(185,177),
   (217,137),(233,8),(241,48),(62,24),(94,66),(158,134),(110,34),(174,168),
   (206,140),(118,86),(182,178),(214,84),(230,224),(122,58),(186,34),(218,74),
   (234,42),(242,96),(124,48),(188,48),(220,4),(236,64),(244,128),(248,0)]

theorem eightFive_covers : validCover 8 5 eightFive = true := by native_decide

end CompleteClauseSeed
