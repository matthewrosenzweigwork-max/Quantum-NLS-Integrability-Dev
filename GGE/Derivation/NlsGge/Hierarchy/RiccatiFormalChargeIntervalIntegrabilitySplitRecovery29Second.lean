import NlsGge.Hierarchy.RiccatiFinitePeriodicMonomialNormalizerUniformRecovery28Seventh
import NlsGge.Hierarchy.RiccatiChargeRemainderSupportOrderBoundsAfterBidegreeThirdRecoveryThird
import NlsGge.Hierarchy.RiccatiJetEvaluationFiniteIntervalSumRecoverySecond
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory
open scoped ContDiff

/-- Actual smooth polynomial jet evaluation is integrable on the fixed source
interval. This isolates the continuity-to-integrability bridge used by the
finite formal-charge expansion. -/
theorem riccatiJetEvaluation_intervalIntegrableNativeRecovery29Second
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (P : Poly) :
    IntervalIntegrable (fun x => riccatiJetEvaluation u x P) volume 0 1 := by
  exact (riccatiJetEvaluation_continuousNativeRecovery u hu P).continuousOn.intervalIntegrable

/-- The actual formal-charge split has an integrable quadratic term and an
integrable nonlinear remainder, so the source integral is the sum of their
integrals on the original period-one interval. -/
theorem formalChargeIntegrand_integral_splitNativeRecovery29Second
    (j : ℕ) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) :
    (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalChargeIntegrand j)) =
      (∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation u x (formalChargeQuadraticMainTerm j)) +
      (∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation u x (formalChargeNonlinearRemainder j)) := by
  have hpoly : formalChargeIntegrand j =
      formalChargeQuadraticMainTerm j + formalChargeNonlinearRemainder j := by
    simp [formalChargeNonlinearRemainder]
  have hq : IntervalIntegrable
      (fun x => riccatiJetEvaluation u x (formalChargeQuadraticMainTerm j)) volume 0 1 :=
    riccatiJetEvaluation_intervalIntegrableNativeRecovery29Second u hu _
  have hr : IntervalIntegrable
      (fun x => riccatiJetEvaluation u x (formalChargeNonlinearRemainder j)) volume 0 1 :=
    riccatiJetEvaluation_intervalIntegrableNativeRecovery29Second u hu _
  rw [hpoly]
  have heval (x : ℝ) :
      riccatiJetEvaluation u x
          (formalChargeQuadraticMainTerm j + formalChargeNonlinearRemainder j) =
        riccatiJetEvaluation u x (formalChargeQuadraticMainTerm j) +
          riccatiJetEvaluation u x (formalChargeNonlinearRemainder j) := by
    simp only [riccatiJetEvaluation, polynomialEvaluation_add]
  calc
    (∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation u x
          (formalChargeQuadraticMainTerm j + formalChargeNonlinearRemainder j)) =
        ∫ x in (0 : ℝ)..1,
          (riccatiJetEvaluation u x (formalChargeQuadraticMainTerm j) +
            riccatiJetEvaluation u x (formalChargeNonlinearRemainder j)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          exact heval x
    _ = _ := intervalIntegral.integral_add hq hr

end NlsGge.HierarchyRiccati.Core

end
