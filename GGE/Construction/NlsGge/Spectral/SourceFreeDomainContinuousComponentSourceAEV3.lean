import NlsGge.Schur.FreeDomainContinuousL2AfterReflectedPrerequisite
import NlsGge.Schur.SourceReflectedIntervalFourierNetV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory

namespace NlsGge.Schur

local instance : IsProbabilityMeasure spectralHaar := by
  unfold spectralHaar
  infer_instance

/-- The continuous Fourier reconstruction, pulled back to the actual source
interval, agrees almost everywhere with the source-coordinate component.
The proof composes the representative equality with the scalar restriction
representative equality; it does not identify arbitrary L² representatives
pointwise. -/
theorem freeDomainContinuousComponent_toSourceInterval_ae
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n)
    (upper : Bool) :
    (fun t : ℝ =>
      ((ContinuousMap.toLp 2 spectralHaar ℂ
        (freeDomainContinuousComponent n x upper) :
          Lp ℂ 2 spectralHaar) ((t : ℝ) : SpectralCircle))) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (sourceCoordinateComponent n x upper : ℝ → ℂ) := by
  have hLp := freeDomainContinuousComponent_toLp n x hx upper
  have hCircle := Lp.ext_iff.mp hLp
  have hF := spectral_ae_pullback_first_half hCircle
  have hP := scalarParityRestrictValue_ae n
    ((parityPairRepr n).symm x upper)
  have hComponent :
      sourceCoordinateComponent n x upper =
        scalarParityRestrictValue n ((parityPairRepr n).symm x upper) := by
    rfl
  filter_upwards [hF, hP] with t hF hP
  change ((ContinuousMap.toLp 2 spectralHaar ℂ
    (freeDomainContinuousComponent n x upper) :
      Lp ℂ 2 spectralHaar) ((t : ℝ) : SpectralCircle)) = _ at hF
  change ((scalarParityRestrictValue n ((parityPairRepr n).symm x upper) :
    SourceIntervalL2) : ℝ → ℂ) t = _ at hP
  calc
    ((ContinuousMap.toLp 2 spectralHaar ℂ
      (freeDomainContinuousComponent n x upper) :
        Lp ℂ 2 spectralHaar) ((t : ℝ) : SpectralCircle)) =
      ((scalarParityRestrictValue n ((parityPairRepr n).symm x upper) :
        SourceIntervalL2) : ℝ → ℂ) t := by
          exact hF.trans hP.symm
    _ = ((sourceCoordinateComponent n x upper : SourceIntervalL2) :
        ℝ → ℂ) t := by rw [hComponent]

end NlsGge.Schur

end
