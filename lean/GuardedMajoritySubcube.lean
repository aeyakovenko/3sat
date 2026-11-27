import Std

namespace GuardedMajoritySubcube

/-- A point on a shortest path to a closest codeword has the same closest codeword. -/
theorem geodesic_to_closest {α : Type} (dist : α → α → Nat) (code : α → Prop)
    (far middle closest : α) (optimal : ∀ c, code c → dist far closest ≤ dist far c)
    (onPath : dist far closest = dist far middle + dist middle closest)
    (triangle : ∀ c, dist far c ≤ dist far middle + dist middle c) :
    ∀ c, code c → dist middle closest ≤ dist middle c := by
  intro c hc
  have hlo := optimal c hc
  have hhi := triangle c
  omega

end GuardedMajoritySubcube
