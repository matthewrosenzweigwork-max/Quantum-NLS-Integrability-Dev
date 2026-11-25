import NlsGge.GK38.Lib.RemovableAnalytic

/-!
# Analytic extension across finitely many analytic subvarieties

This is the packet-facing wrapper for the scalar finite-family extension theorem in the GK38
library. The disc hypothesis is stated with its full radius and containment quantifiers.
-/

set_option autoImplicit false

namespace NlsGge.Atomic.G4

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {U : Set E} {f : E → ℂ}

/-- A continuous scalar function on an open subset of a complex normed space, analytic away from
finitely many analytic subvarieties and analytic on each contained affine disc in each
subvariety, is analytic on the whole open set. -/
theorem analyticOnNhd_of_subvariety_extension {ι : Type*} [Finite ι]
    {V : ι → Set E} (hU : IsOpen U)
    (hV : ∀ i, NlsGge.GK38.Lib.IsAnalyticSubvariety U (V i))
    (hcont : ContinuousOn f U)
    (hoff : AnalyticOnNhd ℂ f (U \ ⋃ i, V i))
    (hdisc : ∀ i, ∀ x ∈ U, ∀ h : E, ∀ r > 0,
      (∀ ζ : ℂ, ‖ζ‖ < r → x + ζ • h ∈ V i ∩ U) →
        AnalyticAt ℂ (fun ζ : ℂ => f (x + ζ • h)) 0) :
    AnalyticOnNhd ℂ f U :=
  NlsGge.GK38.Lib.analyticOnNhd_of_continuous_of_analytic_off_subvarieties
    hU hV hcont hoff hdisc

end NlsGge.Atomic.G4
