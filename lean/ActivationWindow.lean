import Std

namespace ActivationWindow

/-- Until the desired event happens, every missed stage strictly decreases
    a finite nonnegative budget. -/
theorem first_hit (left : Nat → Nat) (hit : Nat → Prop) (bound : Nat)
    (initial : left 0 ≤ bound)
    (spend : ∀ i ≤ bound, (∀ t ≤ i, ¬ hit t) → left (i+1) < left i) :
    ∃ t ≤ bound, hit t := by
  by_cases done : ∃ t ≤ bound, hit t
  · exact done
  · have absent : ∀ i ≤ bound, ¬ hit i := by
      intro i hi hh
      exact done ⟨i, hi, hh⟩
    have spent : ∀ i, i ≤ bound+1 → left i + i ≤ bound := by
      intro i
      induction i with
      | zero => simpa using (fun _ : 0 ≤ bound+1 => initial)
      | succ i ih =>
        intro hi
        have old := ih (by omega)
        have drop := spend i (by omega) (fun t ht => absent t (by omega))
        omega
    have bad := spent (bound+1) (by omega)
    omega

/-- The new always-signalling requirement has at most e eligible predecessors.
    A miss before its first award consumes one. A wholly occupied frame also
    consumes one active requirement per slot; there are at most e+1 of them. -/
theorem two_signs (e : Nat) (earlier active : Nat → Nat)
    (wins idle zero one : Nat → Prop)
    (smallEarlier : earlier 0 ≤ e) (smallActive : active 0 ≤ e+1)
    (preempt : ∀ i ≤ e, (∀ t ≤ i, ¬ wins t) → earlier (i+1) < earlier i)
    (award : ∀ i ≤ e+1, ¬ idle i → active (i+1) < active i)
    (winSign : ∀ t, wins t → zero t) (idleSign : ∀ t, idle t → one t) :
    (∃ t ≤ e, wins t ∧ zero t) ∧ (∃ t ≤ e+1, idle t ∧ one t) := by
  obtain ⟨t, ht, hw⟩ := first_hit earlier wins e smallEarlier preempt
  obtain ⟨u, hu, hd⟩ := first_hit active idle (e+1) smallActive
    (fun i hi noneYet => award i hi (noneYet i (by omega)))
  exact ⟨⟨t,ht,hw,winSign t hw⟩,⟨u,hu,hd,idleSign u hd⟩⟩

end ActivationWindow
