import NlsGge.GK38.Lib.WeaklyAnalytic

set_option autoImplicit false

/-!
# G4-004: weak analyticity plus local boundedness

The pinned project library proves the complex Banach-space criterion of GK A.3
in `NlsGge.GK38.Lib.analyticOnNhd_of_weak_of_locBdd`. This file exports the
campaign-facing bridge using the project's actual `WeaklyAnalyticOn` and
`LocBdd` carriers. In particular, `LocBdd U f` unfolds to the local ball bound
used by the library proof; no Frechet analyticity premise is introduced.
-/

namespace NlsGge.Atomic.G4

theorem analyticOnNhd_of_weakAnalytic_locallyBounded
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set E} {f : E → F}
    (hU : IsOpen U)
    (hweak : NlsGge.GK38.Lib.WeaklyAnalyticOn f U)
    (hbd : NlsGge.GK38.Lib.LocBdd U f) :
    AnalyticOnNhd ℂ f U := by
  exact NlsGge.GK38.Lib.analyticOnNhd_of_weak_of_locBdd hU hweak hbd

end NlsGge.Atomic.G4
