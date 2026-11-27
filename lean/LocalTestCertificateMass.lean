import Std

namespace LocalTestCertificateMass

/-- One node has a forced failed outcome among its equally likely padded
    test outcomes. Only continuing outcomes occur in its list. -/
inductive Tree where
  | stop
  | check (children : List Tree)

def surviving : Nat → Tree → Nat
  | 0, _ => 1
  | _ + 1, .stop => 0
  | h + 1, .check kids => (kids.map (surviving h)).sum

inductive Bounded (cap : Nat) : Tree → Prop where
  | stop : Bounded cap .stop
  | check (kids : List Tree) :
      kids.length ≤ cap → (∀ t ∈ kids, Bounded cap t) → Bounded cap (.check kids)

theorem sum_map_le (kids : List Tree) (f : Tree → Nat) (b : Nat)
    (h : ∀ t ∈ kids, f t ≤ b) : (kids.map f).sum ≤ kids.length * b := by
  induction kids with
  | nil => simp
  | cons t ts ih =>
    have ht := h t (List.mem_cons_self ..)
    have hs := ih (fun u hu => h u (List.mem_cons_of_mem _ hu))
    simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add ht hs

theorem survive_bound (cap h : Nat) (tree : Tree) (hb : Bounded cap tree) :
    surviving h tree ≤ cap^h := by
  induction h generalizing tree with
  | zero => simp [surviving]
  | succ h ih =>
    cases hb with
    | stop => simp [surviving]
    | check kids hlen hkids =>
      have hsum := sum_map_le kids (surviving h) (cap^h)
        (fun t ht => ih t (hkids t ht))
      calc
        surviving (h+1) (.check kids) ≤ kids.length * cap^h := hsum
        _ ≤ cap * cap^h := Nat.mul_le_mul_right _ hlen
        _ = cap^(h+1) := by simp [Nat.pow_succ, Nat.mul_comm]

end LocalTestCertificateMass
