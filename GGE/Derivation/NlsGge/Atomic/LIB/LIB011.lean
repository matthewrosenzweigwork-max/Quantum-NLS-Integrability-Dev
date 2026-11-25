import Mathlib.Analysis.Complex.LocallyUniformLimit

set_option autoImplicit false

namespace NlsGge.Atomic.LIB

open Filter

/-- A locally uniform limit of scalar holomorphic functions on an open subset of `ℂ`
is holomorphic there. The convergence hypothesis retains the locally uniform-on-domain
meaning of `TendstoLocallyUniformlyOn`. -/
theorem analyticOnNhd_of_locallyUniformLimit {U : Set ℂ} {f : ℕ → ℂ → ℂ}
    {g : ℂ → ℂ} (hU : IsOpen U) (ha : ∀ n, AnalyticOnNhd ℂ (f n) U)
    (ht : TendstoLocallyUniformlyOn f g atTop U) : AnalyticOnNhd ℂ g U := by
  have hF : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (f n) U :=
    Filter.Eventually.of_forall fun n => (ha n).differentiableOn
  exact (ht.differentiableOn hF hU).analyticOnNhd hU

end NlsGge.Atomic.LIB
