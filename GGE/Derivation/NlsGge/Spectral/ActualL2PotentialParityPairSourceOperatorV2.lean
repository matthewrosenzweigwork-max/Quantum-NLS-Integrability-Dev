import NlsGge.Spectral.ActualL2PotentialTimesLInfStateV1
import Mathlib.Analysis.Normed.Lp.PiLp

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot

/-- Actual source-interval L∞ states in the two reflected channels. -/
abbrev ActualSourceIntervalLInfPair :=
  PiLp 2 (fun _ : Bool =>
    Lp ℂ ∞ (volume.restrict (Set.Ioc (0 : ℝ) 1)))

/-- The two independent physical L² fields act off-diagonally on actual
source-interval states. The upper output uses `u₁` on the lower input and the
lower output uses `u₂` on the upper input; no conjugacy relation is imposed. -/
def actualL2PotentialParityPairSourceOperator (u₁ u₂ : PhysicalL2) :
    ActualSourceIntervalLInfPair →L[ℂ]
      PiLp 2 (fun _ : Bool => SourceIntervalL2) := by
  let eIn := PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : Bool => Lp ℂ ∞ (volume.restrict (Set.Ioc (0 : ℝ) 1)))
  let eOut := PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : Bool => SourceIntervalL2)
  let f : (Bool → Lp ℂ ∞ (volume.restrict (Set.Ioc (0 : ℝ) 1))) →L[ℂ]
      (Bool → SourceIntervalL2) :=
    ContinuousLinearMap.pi (fun b : Bool =>
      if b then
        (actualSourceL2PotentialTimesLInf u₁).comp
          (ContinuousLinearMap.proj false)
      else
        (actualSourceL2PotentialTimesLInf u₂).comp
          (ContinuousLinearMap.proj true))
  exact eOut.symm.toContinuousLinearMap.comp
    (f.comp eIn.toContinuousLinearMap)

@[simp] theorem actualL2PotentialParityPairSourceOperator_apply_true
    (u₁ u₂ : PhysicalL2) (f : ActualSourceIntervalLInfPair) :
    actualL2PotentialParityPairSourceOperator u₁ u₂ f true =
      actualSourceL2PotentialTimesLInf u₁ (f false) := by
  simp [actualL2PotentialParityPairSourceOperator]

@[simp] theorem actualL2PotentialParityPairSourceOperator_apply_false
    (u₁ u₂ : PhysicalL2) (f : ActualSourceIntervalLInfPair) :
    actualL2PotentialParityPairSourceOperator u₁ u₂ f false =
      actualSourceL2PotentialTimesLInf u₂ (f true) := by
  simp [actualL2PotentialParityPairSourceOperator]

end NlsGge.Schur

end
