import NlsGge.Spectral.ActualFullImaginaryFreeResolventContinuousNormBoundV4
import NlsGge.Spectral.ActualL2PotentialParityPairSourceOperatorV2
import NlsGge.Spectral.ActualPhysicalL2SourcePotentialRepresentativeV1
import NlsGge.Spectral.ActualContinuousResolventIntervalLInfV4
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot

/-- The two actual interval-L-infinity states obtained from the full imaginary
free resolvent, preserving the true upper/lower channel order of
`sourcePairRepr`. -/
def actualFullImaginaryResolventIntervalLInfPair
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SourcePairL2) :
    ActualSourceIntervalLInfPair :=
  WithLp.toLp 2 (fun b : Bool =>
    actualFullImaginaryResolventIntervalLInf n y hy x b)

theorem actualFullImaginaryResolventIntervalLInfPair_apply
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SourcePairL2) (b : Bool) :
    actualFullImaginaryResolventIntervalLInfPair n y hy x b =
      actualFullImaginaryResolventIntervalLInf n y hy x b := rfl

/-- The actual off-diagonal upper source product is the physical first field
multiplied by the continuous lower resolvent representative, almost
Everywhere on the actual source interval. -/
theorem actualRoughL2PotentialFullImaginaryResolvent_upper_ae
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2)
    (x : SourcePairL2) :
    (actualL2PotentialParityPairSourceOperator u₁ u₂
      (actualFullImaginaryResolventIntervalLInfPair n y hy x) true : ℝ → ℂ) =ᵐ[
        volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun t => u₁ ((t : ℝ) : PhysicalCircle) *
        freeDomainContinuousComponent n
          (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x)) false
          ((t : ℝ) : SpectralCircle) := by
  rw [actualL2PotentialParityPairSourceOperator_apply_true]
  have hmul := actualSourceL2PotentialTimesLInf_ae u₁
    (actualFullImaginaryResolventIntervalLInf n y hy x false)
  have hu := actualPhysicalL2SourcePotential_ae u₁
  have hr := actualFullImaginaryResolventIntervalLInf_ae n y hy x false
  filter_upwards [hmul, hu, hr] with t hmul hu hr
  calc
    actualSourceL2PotentialTimesLInf u₁
        (actualFullImaginaryResolventIntervalLInf n y hy x false) t =
        actualPhysicalL2SourcePotential u₁ t *
          actualFullImaginaryResolventIntervalLInf n y hy x false t := hmul
    _ = u₁ ((t : ℝ) : PhysicalCircle) *
        freeDomainContinuousComponent n
          (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x)) false
          ((t : ℝ) : SpectralCircle) := by rw [hu, hr]

/-- The actual off-diagonal lower source product is the physical second field
multiplied by the continuous upper resolvent representative, almost
Everywhere on the actual source interval. -/
theorem actualRoughL2PotentialFullImaginaryResolvent_lower_ae
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2)
    (x : SourcePairL2) :
    (actualL2PotentialParityPairSourceOperator u₁ u₂
      (actualFullImaginaryResolventIntervalLInfPair n y hy x) false : ℝ → ℂ) =ᵐ[
        volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun t => u₂ ((t : ℝ) : PhysicalCircle) *
        freeDomainContinuousComponent n
          (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x)) true
          ((t : ℝ) : SpectralCircle) := by
  rw [actualL2PotentialParityPairSourceOperator_apply_false]
  have hmul := actualSourceL2PotentialTimesLInf_ae u₂
    (actualFullImaginaryResolventIntervalLInf n y hy x true)
  have hu := actualPhysicalL2SourcePotential_ae u₂
  have hr := actualFullImaginaryResolventIntervalLInf_ae n y hy x true
  filter_upwards [hmul, hu, hr] with t hmul hu hr
  calc
    actualSourceL2PotentialTimesLInf u₂
        (actualFullImaginaryResolventIntervalLInf n y hy x true) t =
        actualPhysicalL2SourcePotential u₂ t *
          actualFullImaginaryResolventIntervalLInf n y hy x true t := hmul
    _ = u₂ ((t : ℝ) : PhysicalCircle) *
        freeDomainContinuousComponent n
          (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x)) true
          ((t : ℝ) : SpectralCircle) := by rw [hu, hr]

private theorem actualRoughPotentialResolventUpperComponent_bound
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2)
    (x : SourcePairL2) :
    ‖actualL2PotentialParityPairSourceOperator u₁ u₂
      (actualFullImaginaryResolventIntervalLInfPair n y hy x) true‖ ≤
      ‖u₁‖ * (Real.sqrt (2 / y) * ‖x‖) := by
  rw [actualL2PotentialParityPairSourceOperator_apply_true]
  calc
    ‖actualSourceL2PotentialTimesLInf u₁
        (actualFullImaginaryResolventIntervalLInf n y hy x false)‖ ≤
        ‖actualSourceL2PotentialTimesLInf u₁‖ *
          ‖actualFullImaginaryResolventIntervalLInf n y hy x false‖ :=
      (actualSourceL2PotentialTimesLInf u₁).le_opNorm _
    _ ≤ ‖u₁‖ * (Real.sqrt (2 / y) * ‖x‖) :=
      mul_le_mul
        (actualSourceL2PotentialTimesLInf_norm_bound u₁)
        (actualFullImaginaryResolventIntervalLInf_norm_le n y hy x false)
        (norm_nonneg _) (norm_nonneg _)

private theorem actualRoughPotentialResolventLowerComponent_bound
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2)
    (x : SourcePairL2) :
    ‖actualL2PotentialParityPairSourceOperator u₁ u₂
      (actualFullImaginaryResolventIntervalLInfPair n y hy x) false‖ ≤
      ‖u₂‖ * (Real.sqrt (2 / y) * ‖x‖) := by
  rw [actualL2PotentialParityPairSourceOperator_apply_false]
  calc
    ‖actualSourceL2PotentialTimesLInf u₂
        (actualFullImaginaryResolventIntervalLInf n y hy x true)‖ ≤
        ‖actualSourceL2PotentialTimesLInf u₂‖ *
          ‖actualFullImaginaryResolventIntervalLInf n y hy x true‖ :=
      (actualSourceL2PotentialTimesLInf u₂).le_opNorm _
    _ ≤ ‖u₂‖ * (Real.sqrt (2 / y) * ‖x‖) :=
      mul_le_mul
        (actualSourceL2PotentialTimesLInf_norm_bound u₂)
        (actualFullImaginaryResolventIntervalLInf_norm_le n y hy x true)
        (norm_nonneg _) (norm_nonneg _)

/-- For arbitrary independent physical L² fields, the actual two-channel
source multiplication composed with the full imaginary free resolvent satisfies
pointwise decay `sqrt (2/y) * (‖u₁‖₂+‖u₂‖₂) * ‖x‖`. The estimate uses the
actual interval representatives and actual L²×L-infinity source multiplier. -/
theorem actualRoughL2PotentialTimesFullImaginaryResolvent_norm_le
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2)
    (x : SourcePairL2) :
    ‖actualL2PotentialParityPairSourceOperator u₁ u₂
      (actualFullImaginaryResolventIntervalLInfPair n y hy x)‖ ≤
      Real.sqrt (2 / y) * (‖u₁‖ + ‖u₂‖) * ‖x‖ := by
  let T := actualL2PotentialParityPairSourceOperator u₁ u₂
    (actualFullImaginaryResolventIntervalLInfPair n y hy x)
  let A := Real.sqrt (2 / y) * ‖x‖
  have hA : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have h1 := actualRoughPotentialResolventUpperComponent_bound n y hy u₁ u₂ x
  have h2 := actualRoughPotentialResolventLowerComponent_bound n y hy u₁ u₂ x
  have h1sq : ‖T true‖ ^ 2 ≤ (‖u₁‖ * A) ^ 2 := by
    dsimp [T, A] at h1 ⊢
    nlinarith [norm_nonneg (actualL2PotentialParityPairSourceOperator u₁ u₂
      (actualFullImaginaryResolventIntervalLInfPair n y hy x) true)]
  have h2sq : ‖T false‖ ^ 2 ≤ (‖u₂‖ * A) ^ 2 := by
    dsimp [T, A] at h2 ⊢
    nlinarith [norm_nonneg (actualL2PotentialParityPairSourceOperator u₁ u₂
      (actualFullImaginaryResolventIntervalLInfPair n y hy x) false)]
  have hsum : ‖T true‖ ^ 2 + ‖T false‖ ^ 2 ≤
      ((‖u₁‖ + ‖u₂‖) * A) ^ 2 := by
    have hu₁ : 0 ≤ ‖u₁‖ := norm_nonneg _
    have hu₂ : 0 ≤ ‖u₂‖ := norm_nonneg _
    nlinarith [mul_nonneg (mul_nonneg hu₁ hu₂) (sq_nonneg A), h1sq, h2sq]
  have hnorm := PiLp.norm_eq_of_L2 T
  rw [Fintype.sum_bool] at hnorm
  have hK : 0 ≤ (‖u₁‖ + ‖u₂‖) * A :=
    mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) hA
  calc
    ‖T‖ = Real.sqrt (‖T true‖ ^ 2 + ‖T false‖ ^ 2) := by simpa using hnorm
    _ ≤ Real.sqrt (((‖u₁‖ + ‖u₂‖) * A) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = (‖u₁‖ + ‖u₂‖) * A := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hK]
    _ = Real.sqrt (2 / y) * (‖u₁‖ + ‖u₂‖) * ‖x‖ := by dsimp [A]; ring

end NlsGge.Schur

end
