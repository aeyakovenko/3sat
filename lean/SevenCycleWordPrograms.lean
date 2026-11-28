import Std

namespace SevenCycleWordPrograms

inductive Comparison where | eq | ult | slt
inductive Program where
  | yes | no | ld (address : Nat) (next : Program)
  | br (comparison : Comparison) (a b : Nat) (yes no : Program)
open Program

/-- Operands 0..7 are immediate literals. Operands 8, 9 and 10 hold loaded input words. -/
def operand (mask loaded index : Nat) : Option Nat :=
  if index < 8 then some index
  else if index < 11 && loaded.testBit (index-8) then some ((mask >>> (3*(index-8))) % 8)
  else none

def compareWord : Comparison → Nat → Nat → Bool
  | .eq,a,b => a == b
  | .ult,a,b => decide (a < b)
  | .slt,a,b => decide ((a ^^^ 4) < (b ^^^ 4))

/-- A return is free. Every native load or branch uses one tick. Missing loads fail. -/
def run (mask : Nat) : Program → Nat → Nat → Option Bool
  | .yes, _, _ => some true
  | .no, _, _ => some false
  | .ld _ _, _, 0 => none
  | .br _ _ _ _ _, _, 0 => none
  | .ld a next, loaded, t+1 =>
    if a < 3 then run mask next (loaded ||| (1 <<< a)) t else none
  | .br op a b yesBranch noBranch, loaded, t+1 => do
    let x ← operand mask loaded a
    let y ← operand mask loaded b
    if compareWord op x y then run mask yesBranch loaded t else run mask noBranch loaded t

def cover (mask : Nat) : Bool :=
  (List.range 7).all fun i => mask.testBit i || mask.testBit ((i+1)%7)

def subdivide (useOr : Bool) (gap v : Nat) : Nat :=
  let a := v.testBit gap
  let b := v.testBit ((gap+1)%6)
  let inserted := if useOr then a || b else xor a b
  let boundary := 1 <<< (gap+1)
  v%boundary + inserted.toNat*boundary + 2*(v/boundary)*boundary

def xorGap0 : Program :=
  (ld 0 (br .ult 8 4
    (br .eq 8 0
      no
      (ld 1 (br .eq 8 9
          (ld 2 (br .eq 10 0
              no
              yes))
          (br .eq 9 5
            yes
            (br .eq 9 7
              yes
              no)))))
    (ld 1 (br .ult 9 5
        (br .slt 9 2
          no
          (ld 2 (br .eq 10 0
              no
              yes)))
        (br .eq 8 5
          yes
          (ld 2 (br .eq 10 0
              no
              yes)))))))

def xorGap1 : Program :=
  (ld 0 (br .ult 8 5
    (ld 1 (ld 2 (br .eq 10 0
          (br .eq 8 3
            (br .ult 8 9
              yes
              no)
            no)
          (br .eq 9 10
            no
            (br .slt 8 2
              no
              yes)))))
    (ld 1 (br .eq 8 9
        (br .eq 8 5
          yes
          (ld 2 (br .eq 10 0
              no
              yes)))
        (br .slt 9 2
          (br .eq 8 5
            (br .eq 9 1
              no
              yes)
            (br .eq 9 6
              yes
              no))
          (ld 2 (br .eq 10 0
              no
              yes)))))))

def xorGap2 : Program :=
  (ld 0 (ld 1 (br .ult 8 9
      (br .eq 8 2
        (br .eq 9 4
          no
          (ld 2 (br .eq 10 0
              no
              yes)))
        (br .eq 8 0
          no
          (br .eq 8 3
            (br .eq 9 4
              no
              yes)
            (br .eq 8 5
              yes
              no))))
      (ld 2 (br .eq 10 0
          (br .eq 8 6
            no
            (br .ult 9 4
              no
              yes))
          (br .eq 8 4
            no
            (br .ult 9 2
              no
              yes)))))))

def xorGap3 : Program :=
  (ld 0 (ld 1 (br .ult 8 9
      (br .eq 8 2
        (br .eq 9 6
          no
          (ld 2 (br .eq 10 0
              no
              yes)))
        (br .eq 8 0
          no
          (br .eq 8 3
            (br .eq 9 5
              yes
              no)
            (br .eq 8 5
              yes
              no))))
      (ld 2 (br .eq 10 0
          (br .eq 8 6
            no
            (br .ult 9 4
              no
              yes))
          (br .eq 8 4
            no
            (br .eq 9 0
              no
              yes)))))))

def xorGap4 : Program :=
  (ld 0 (br .slt 8 2
    (ld 1 (br .ult 9 8
        (br .slt 9 2
          (br .ult 9 5
            no
            yes)
          (br .eq 8 4
            no
            yes))
        (br .eq 8 5
          yes
          (br .eq 8 7
            yes
            no))))
    (br .eq 8 2
      (ld 1 (br .eq 9 3
          yes
          (br .eq 9 5
            yes
            no)))
      (ld 1 (br .ult 9 5
          (br .eq 8 9
            yes
            no)
          (br .eq 9 6
            no
            yes))))))

def xorGap5 : Program :=
  (ld 0 (br .ult 8 4
    (ld 1 (br .ult 9 5
        (br .eq 8 9
          (br .eq 8 3
            yes
            no)
          no)
        (br .eq 9 6
          no
          (br .ult 8 2
            no
            yes))))
    (br .eq 8 4
      no
      (ld 1 (br .slt 9 2
          (br .ult 9 5
            no
            yes)
          (br .eq 8 6
            no
            yes))))))

def orGap0 : Program :=
  (ld 0 (br .ult 8 4
    (br .eq 8 0
      no
      (ld 1 (br .eq 8 9
          (ld 2 (br .eq 10 0
              no
              yes))
          (br .eq 9 5
            yes
            (br .eq 9 7
              yes
              no)))))
    (ld 1 (br .ult 9 5
        (br .slt 9 2
          no
          (ld 2 (br .eq 10 0
              no
              yes)))
        (br .eq 8 6
          (ld 2 (br .eq 10 0
              no
              yes))
          yes)))))

def orGap1 : Program :=
  (ld 0 (br .eq 8 6
    (ld 1 (br .eq 9 4
        no
        (br .ult 9 2
          no
          (ld 2 (br .eq 10 0
              no
              yes)))))
    (br .ult 8 5
      no
      (ld 1 (br .slt 9 2
          (br .eq 8 9
            yes
            (br .ult 9 5
              no
              yes))
          (ld 2 (br .eq 10 0
              no
              yes)))))))

def orGap2 : Program :=
  (ld 0 (ld 1 (br .ult 8 9
      (br .eq 8 2
        (br .eq 9 4
          no
          (ld 2 (br .eq 10 0
              no
              yes)))
        (br .eq 8 6
          (ld 2 (br .eq 10 0
              no
              yes))
          (br .eq 8 3
            (br .eq 9 4
              no
              yes)
            (br .eq 8 5
              yes
              no))))
      (ld 2 (br .eq 10 0
          (br .eq 8 6
            no
            (br .ult 9 4
              no
              yes))
          (br .eq 8 4
            no
            (br .ult 9 2
              no
              yes)))))))

def orGap3 : Program :=
  (ld 0 (ld 1 (br .ult 8 9
      (br .eq 8 2
        (br .eq 9 6
          no
          (ld 2 (br .eq 10 0
              no
              yes)))
        (br .eq 8 6
          (ld 2 (br .eq 10 0
              no
              yes))
          (br .eq 8 3
            (br .eq 9 6
              no
              yes)
            (br .eq 8 5
              yes
              no))))
      (ld 2 (br .eq 10 0
          (br .eq 8 9
            (br .eq 8 7
              yes
              no)
            (br .eq 9 6
              yes
              no))
          (br .eq 8 4
            no
            (br .eq 9 0
              no
              yes)))))))

def orGap4 : Program :=
  (ld 0 (br .eq 8 2
    (ld 1 (br .eq 9 0
        no
        (br .eq 9 7
          (ld 2 (br .eq 10 0
              no
              yes))
          (br .eq 9 1
            no
            (br .eq 9 5
              yes
              no)))))
    (br .eq 8 6
      (ld 1 (br .eq 9 4
          no
          (ld 2 (br .eq 10 0
              no
              yes))))
      (br .eq 8 3
        (ld 1 (br .eq 9 5
            yes
            (br .eq 9 7
              yes
              no)))
        (br .ult 8 5
          no
          (ld 1 (br .ult 9 5
              no
              yes)))))))

def orGap5 : Program :=
  (ld 0 (br .ult 8 4
    (ld 1 (br .ult 9 5
        (br .eq 8 9
          (br .eq 8 3
            yes
            no)
          no)
        (br .eq 9 6
          no
          (br .ult 8 2
            no
            yes))))
    (br .eq 8 4
      no
      (ld 1 (br .slt 9 2
          (br .ult 9 5
            no
            yes)
          (br .eq 8 6
            no
            yes))))))

def full : Program :=
  (ld 0 (br .eq 8 2
    (ld 1 (br .eq 8 9
        no
        (br .ult 9 5
          (br .eq 9 3
            (ld 2 (br .eq 10 0
                no
                yes))
            no)
          (br .eq 9 6
            no
            (ld 2 (br .eq 10 0
                no
                yes))))))
    (br .ult 8 5
      (br .eq 8 3
        (ld 1 (br .eq 8 9
            (ld 2 (br .eq 10 0
                no
                yes))
            (br .eq 9 5
              yes
              (br .eq 9 7
                yes
                no))))
        no)
      (ld 1 (br .ult 9 5
          (br .slt 9 2
            no
            (ld 2 (br .eq 10 0
                no
                yes)))
          (br .eq 8 6
            (ld 2 (br .eq 10 0
                no
                yes))
            yes))))))

def cases : List (Bool × Nat × Nat × Program) := [
  (false, 0, 7, xorGap0),
  (false, 1, 7, xorGap1),
  (false, 2, 7, xorGap2),
  (false, 3, 7, xorGap3),
  (false, 4, 6, xorGap4),
  (false, 5, 6, xorGap5),
  (true, 0, 7, orGap0),
  (true, 1, 7, orGap1),
  (true, 2, 7, orGap2),
  (true, 3, 7, orGap3),
  (true, 4, 7, orGap4),
  (true, 5, 6, orGap5)]

/-- All twelve subdivision programs return the correct verdict within the displayed clocks. -/
theorem all_subdivisions : cases.all (fun (useOr,gap,t,p) =>
    (List.range 64).all (fun old =>
      let mask := subdivide useOr gap old
      run mask p 0 t == some (cover mask))) = true := by native_decide

theorem complete_seven_bit_upper : ∀ i : Fin 128,
    run i.val full 0 8 = some (cover i.val) := by native_decide

end SevenCycleWordPrograms
