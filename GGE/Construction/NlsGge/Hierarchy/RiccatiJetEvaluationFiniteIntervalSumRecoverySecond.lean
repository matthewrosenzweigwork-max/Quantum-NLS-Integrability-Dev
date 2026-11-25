import NlsGge.Hierarchy.RiccatiMonomialPeriodicIBPStepRecoveryThird
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory
open scoped ContDiff

/-- Evaluation and integration both distribute over a finite polynomial sum
for the actual smooth jet evaluator; continuity supplies each interval
integrability premise. -/
theorem riccatiJetEvaluation_integral_finset_sumNativeRecoverySecond
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    {ι : Type*} (s : Finset ι) (P : ι → Poly) :
    (∫ x in (0 : ℝ)..1,
      riccatiJetEvaluation u x (∑ i ∈ s, P i)) =
      ∑ i ∈ s, ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (P i) := by
  classical
  calc
    (∫ x in (0 : ℝ)..1,
      riccatiJetEvaluation u x (∑ i ∈ s, P i)) =
        ∫ x in (0 : ℝ)..1,
          ∑ i ∈ s, riccatiJetEvaluation u x (P i) := by
            apply intervalIntegral.integral_congr
            intro x hx
            simp [riccatiJetEvaluation, polynomialEvaluation, map_sum]
    _ = ∑ i ∈ s, ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (P i) :=
      intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume)
        (a := (0 : ℝ)) (b := 1) (fun i hi => by
          exact (riccatiJetEvaluation_continuousNativeRecovery u hu (P i)).continuousOn.intervalIntegrable)

end NlsGge.HierarchyRiccati.Core

end
