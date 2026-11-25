import NlsGge.Schur.PhysicalH1ComplexCanonicalRepresentativeAfterCarrier
import NlsGge.Analysis.CoveredH1Field
import NlsGge.Schur.CoveredH1SpectralMultiplier
import NlsGge.Schur.SourceInterval
import Mathlib.MeasureTheory.Function.Holder

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

open NlsGge.Pilot NlsGge.Analysis
open MeasureTheory
open scoped ENNReal

local notation "H1WeightMul22" => sobolevModeWeight (1 : ℝ)

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

local instance : IsProbabilityMeasure spectralHaar := by
  unfold spectralHaar
  infer_instance

/-- The genuine degree-two lifted H¹ field is a complex-linear continuous map
from the weighted complex Fourier carrier into spectral L∞. -/
def physicalH1ComplexCoverBoundedFieldCLM22 :
    WeightedHilbert H1WeightMul22 →L[ℂ] Lp ℂ ∞ spectralHaar := by
  let toLp : C(PhysicalCircle, ℂ) →L[ℂ] Lp ℂ ∞ spatialMeasure :=
    ContinuousMap.toLp ∞ spatialMeasure ℂ
  let cover : Lp ℂ ∞ spatialMeasure →L[ℂ] Lp ℂ ∞ spectralHaar :=
    (Lp.compMeasurePreservingₗᵢ ℂ naturalPhysicalCover
      naturalPhysicalCover_preserving).toContinuousLinearMap
  exact cover.comp (toLp.comp physicalH1ComplexCanonicalRepresentativeCLM22)

/-- The actual scalar multiplication operator depends complex-linearly on the
complex H¹ field, via the pinned Hölder bilinear map. -/
def physicalH1ComplexScalarMultiplierParameterCLM22 :
    WeightedHilbert H1WeightMul22 →L[ℂ]
      (SpectralScalarL2 →L[ℂ] SpectralScalarL2) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL spectralHaar ∞ 2 2 |>.comp
    physicalH1ComplexCoverBoundedFieldCLM22

theorem physicalH1ComplexCoverBoundedFieldCLM22_apply
    (x : WeightedHilbert H1WeightMul22) :
    physicalH1ComplexCoverBoundedFieldCLM22 x =
      naturalPhysicalCoverH1Bounded
        (physicalH1ComplexCarrierToL2Actual22 x)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x) := rfl

theorem physicalH1ComplexScalarMultiplierParameterCLM22_apply
    (x : WeightedHilbert H1WeightMul22) :
    physicalH1ComplexScalarMultiplierParameterCLM22 x =
      coveredH1SpectralMultiplier
        (physicalH1ComplexCarrierToL2Actual22 x)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x) := rfl

end NlsGge.Schur
