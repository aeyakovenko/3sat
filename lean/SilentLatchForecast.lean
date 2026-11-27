import Std

namespace SilentLatchForecast

/-- The bit sampled at the observation. A preceding halt returning v has
    written its complement. Before such a halt the verdict track contains zero. -/
def latch : Option Bool → Bool
  | none => false
  | some verdict => !verdict

/-- On a recognizer's own header the pending computation can only report
    false. If that report must agree with the forecast, it cannot arrive
    before observation, and the forecast equals the untouched zero. -/
theorem silent (early : Option Bool) (forecast : Bool)
    (own : forecast = latch early)
    (negativeOnly : early ≠ some true)
    (sound : early = some false → forecast = false) :
    early = none ∧ forecast = false := by
  cases early with
  | none => exact ⟨rfl, own⟩
  | some verdict =>
    cases verdict with
    | true => exact False.elim (negativeOnly rfl)
    | false =>
      have contradiction : (false : Bool) = true := (sound rfl).symm.trans own
      cases contradiction

/-- A successful search has checked a certificate and returns the negative
    verdict. Its elapsed time includes everything needed to latch the result.
    A halt exactly at the deadline is outside the pre-observation interval. -/
def earlyNegative {Certificate : Type} (deadline : Nat)
    (search : Option (Nat × Certificate)) : Option Bool :=
  match search with
  | none => none
  | some (finish, _) => if finish < deadline then some false else none

/-- The machine model supplies the own-header equation and the elapsed time.
    No assumption that the search finds every valid certificate is needed. -/
theorem own_header {Certificate : Type} (deadline : Nat)
    (search : Option (Nat × Certificate)) (forecast : Bool)
    (valid : Certificate → Prop)
    (own : forecast = latch (earlyNegative deadline search))
    (onlyValid : ∀ t c, search = some (t,c) → valid c)
    (sound : ∀ c, valid c → forecast = false) :
    forecast = false ∧ ∀ t c, search = some (t,c) → deadline ≤ t := by
  have oneSided : earlyNegative deadline search ≠ some true := by
    cases search with
    | none => simp [earlyNegative]
    | some x =>
      rcases x with ⟨finish, cert⟩
      simp only [earlyNegative]
      split <;> decide
  have reportsTrue : earlyNegative deadline search = some false → forecast = false := by
    intro report
    cases hs : search with
    | none => simp [hs, earlyNegative] at report
    | some x =>
      rcases x with ⟨finish, cert⟩
      exact sound cert (onlyValid finish cert hs)
  obtain ⟨quiet, zero⟩ := silent _ _ own oneSided reportsTrue
  refine ⟨zero, ?_⟩
  intro finish cert emitted
  by_cases before : finish < deadline
  · simp [emitted, earlyNegative, before] at quiet
  · omega

/-- Applies to all certificates a stated running-time guarantee would cover.
    Completeness for arbitrary certificates is a separate hypothesis. -/
theorem no_covered_certificate {Certificate : Type} (deadline : Nat)
    (search : Option (Nat × Certificate)) (valid : Certificate → Prop)
    (tooLate : ∀ t c, search = some (t,c) → deadline ≤ t)
    (cost : Certificate → Nat) (budget : Nat)
    (coverage : ∀ c, valid c → cost c ≤ budget →
      ∃ t found, search = some (t,found) ∧ t < deadline) :
    ∀ c, valid c → budget < cost c := by
  intro c correct
  by_cases short : cost c ≤ budget
  · obtain ⟨t,found,emitted,early⟩ := coverage c correct short
    have late := tooLate t found emitted
    omega
  · omega

/-- A proposed fast procedure may be a compiler followed by a SAT solver.
    Its assumed coverage must concern the actual run on this header. -/
theorem resource_obstruction {Certificate : Type} (deadline : Nat)
    (search : Option (Nat × Certificate)) (forecast : Bool)
    (valid : Certificate → Prop)
    (own : forecast = latch (earlyNegative deadline search))
    (onlyValid : ∀ t c, search = some (t,c) → valid c)
    (sound : ∀ c, valid c → forecast = false)
    (cost budget : Nat)
    (fastOnNegative : forecast = false → cost ≤ budget →
      ∃ t c, search = some (t,c) ∧ t < deadline) :
    forecast = false ∧ budget < cost := by
  obtain ⟨zero, late⟩ := own_header deadline search forecast valid own onlyValid sound
  refine ⟨zero, ?_⟩
  by_cases within : cost ≤ budget
  · obtain ⟨t,c,emitted,early⟩ := fastOnNegative zero within
    have lower := late t c emitted
    omega
  · omega

end SilentLatchForecast
