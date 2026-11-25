import NlsGge.Schur.FreeDomainContinuousTrace
import NlsGge.Measure.ReflectedSectorFourierHasSumPrerequisite

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur

local instance : IsProbabilityMeasure spectralHaar := by
  unfold spectralHaar
  infer_instance

set_option backward.isDefEq.respectTransparency false in

/-- The uniformly convergent source-domain series is a representative of
the original actual parity L² field, in both reflected channels. Endpoint
values proved for this series therefore belong to that genuine field. -/
theorem freeDomainContinuousComponent_toLp
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n)
    (upper : Bool) :
    ContinuousMap.toLp 2 spectralHaar ℂ (freeDomainContinuousComponent n x upper) =
      (((parityPairRepr n).symm x upper : scalarParity n) : SpectralScalarL2) := by
  let f : ParityPair n := (parityPairRepr n).symm x
  have hcoord (m : Sector n) :
      scalarParityRepr n (f upper) (mixedIndex n (upper,m)) = x (upper,m) := by
    calc
      _ = parityPairRepr n f (upper,m) := (parityPairRepr_apply n f (upper,m)).symm
      _ = _ := congrArg (fun y : SectorSquare n => y (upper,m))
        ((parityPairRepr n).apply_symm_apply x)
  have hb := (scalarParityFourierBasis n).hasSum_repr (f upper)
  have hm := (scalarParity n).subtypeL.hasSum hb
  have hm' : HasSum (fun m : Sector n =>
      scalarParityRepr n (f upper) m • spectralBasis m.val)
      ((f upper : scalarParity n) : SpectralScalarL2) := by
    simpa only [map_smul, scalarParityRepr, scalarParityFourierBasis,
      HilbertBasis.coe_mkOfOrthogonalEqBot, scalarParityVector,
      Submodule.subtypeL_apply, Submodule.coe_mk] using hm
  have hc := (ContinuousMap.toLp 2 spectralHaar ℂ).hasSum
    (freeDomainContinuousComponent_hasSum n x hx upper)
  simp only [map_smul] at hc
  change HasSum (fun m : Sector n => x (upper,m) •
      fourierLp (T := (2 : ℝ)) 2 (if upper then m.val else -m.val))
    (ContinuousMap.toLp 2 spectralHaar ℂ (freeDomainContinuousComponent n x upper)) at hc
  cases upper
  · have hr := hasSum_reflectedSector_fourier n
      (fun m => scalarParityRepr n (f false) m) (f false) hm'
    have he : HasSum (fun m : Sector n => x (false,m) •
        fourierLp (T := (2 : ℝ)) 2 (-m.val))
        ((f false : scalarParity n) : SpectralScalarL2) := by
      simpa only [negateIndex_val,
        ← hcoord, mixedIndex, Bool.false_eq_true, if_false, spectralBasis] using hr
    exact hc.unique he
  · have he : HasSum (fun m : Sector n => x (true,m) •
        fourierLp (T := (2 : ℝ)) 2 m.val)
        ((f true : scalarParity n) : SpectralScalarL2) := by
      simpa only [← hcoord, mixedIndex, if_true, spectralBasis] using hm'
    exact hc.unique he

end NlsGge.Schur
