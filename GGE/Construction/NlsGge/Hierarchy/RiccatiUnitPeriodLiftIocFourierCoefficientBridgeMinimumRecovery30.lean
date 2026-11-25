import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

/-- Isolated actual unit-period bridge between the raw AddCircle lift and the
interval-coefficient definition. This contains no source-Sobolev or derivative
agreement assumptions. -/
theorem fourierCoeff_unitPeriod_liftIoc_eq_fourierCoeffOnMinimumRecovery30
    (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (AddCircle.liftIoc (1 : ℝ) (0 : ℝ) f) n =
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n := by
  have h := fourierCoeff_liftIoc_eq (T := (1 : ℝ)) (a := (0 : ℝ)) f n
  simpa only [zero_add] using h

end NlsGge.HierarchyRiccati.Core

end
