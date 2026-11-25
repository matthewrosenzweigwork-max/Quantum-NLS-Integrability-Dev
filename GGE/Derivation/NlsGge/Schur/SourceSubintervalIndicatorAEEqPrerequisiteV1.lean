import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur

/-- Exact a.e. representative of the actual L² indicator on the restricted
source interval. The restricted measure and its finite-set witness are explicit. -/
theorem indicatorConstLp_sourceSubinterval_ae (t : ℝ) :
    let μ : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)
    let S : Set ℝ := Set.Ioc (0 : ℝ) t
    (MeasureTheory.indicatorConstLp (s := S) (μ := μ) (2 : ℝ≥0∞)
      (measurableSet_Ioc : MeasurableSet S)
      (MeasureTheory.measure_lt_top μ S).ne (1 : ℂ) : ℝ → ℂ) =ᵐ[μ]
      S.indicator (fun _ : ℝ => (1 : ℂ)) := by
  exact MeasureTheory.indicatorConstLp_coeFn

end NlsGge.Schur

end
