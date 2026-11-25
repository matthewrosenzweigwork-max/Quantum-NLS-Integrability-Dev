import NlsGge.Analysis.CoveredH1Field
import NlsGge.Schur.FourierMultiplier
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot

/-- Multiplication by the actual H¹ field after its true degree-two lift. -/
def coveredH1SpectralMultiplier (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    SpectralScalarL2 →L[ℂ] SpectralScalarL2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL spectralHaar ∞ 2 2
    (NlsGge.Analysis.naturalPhysicalCoverH1Bounded u hu)

/-- Its value is the genuine pointwise product of actual L² representatives. -/
theorem coveredH1SpectralMultiplier_ae (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (f : SpectralScalarL2) :
    (coveredH1SpectralMultiplier u hu f : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      fun x => NlsGge.Analysis.naturalPhysicalCoverH1Bounded u hu x * f x := by
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := (2 : ℝ≥0∞))
    (NlsGge.Analysis.naturalPhysicalCoverH1Bounded u hu) f
  change (coveredH1SpectralMultiplier u hu f : SpectralCircle → ℂ) =ᵐ[spectralHaar]
    (fun x => NlsGge.Analysis.naturalPhysicalCoverH1Bounded u hu x * f x) at hm
  exact hm

/-- The covered multiplier inherits the source H¹ ball estimate. -/
theorem coveredH1SpectralMultiplier_norm_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖coveredH1SpectralMultiplier u hu‖ ≤
      NlsGge.Analysis.physicalH1MultiplierConstant *
        ‖physicalSobolevL2 1 u hu‖ := by
  have hop : ‖(ContinuousLinearMap.mul ℂ ℂ).holderL spectralHaar ∞ 2 2‖ ≤ 1 := by
    exact (ContinuousLinearMap.norm_holderL_le (ContinuousLinearMap.mul ℂ ℂ)).trans
      (ContinuousLinearMap.opNorm_mul_le ℂ ℂ)
  calc
    ‖coveredH1SpectralMultiplier u hu‖ ≤
        ‖(ContinuousLinearMap.mul ℂ ℂ).holderL spectralHaar ∞ 2 2‖ *
          ‖NlsGge.Analysis.naturalPhysicalCoverH1Bounded u hu‖ :=
      ((ContinuousLinearMap.mul ℂ ℂ).holderL spectralHaar ∞ 2 2).le_opNorm _
    _ ≤ 1 * (NlsGge.Analysis.physicalH1MultiplierConstant *
        ‖physicalSobolevL2 1 u hu‖) := by
      calc
        _ ≤ 1 * ‖NlsGge.Analysis.naturalPhysicalCoverH1Bounded u hu‖ :=
          mul_le_mul_of_nonneg_right hop (norm_nonneg _)
        _ ≤ 1 * (NlsGge.Analysis.physicalH1MultiplierConstant *
            ‖physicalSobolevL2 1 u hu‖) :=
          mul_le_mul_of_nonneg_left
            (NlsGge.Analysis.naturalPhysicalCoverH1Bounded_norm_bound u hu) (by norm_num)
    _ = _ := by ring

end NlsGge.Schur
