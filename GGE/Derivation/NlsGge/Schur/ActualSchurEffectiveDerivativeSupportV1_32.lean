import NlsGge.Schur.ActualSchurEffectiveJointAnalyticAfterDextV3_30
import NlsGge.Schur.ActualSchurGreenProductBoundV3_31
import NlsGge.Schur.ActualSchurGreenSandwichCLMMinimumV3_32

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- The actual total complementary Green family in source order `D S`, at
fixed actual independent complex H¹ pair. This declaration is extracted from
the preserved V3 conditional-derivative source so it depends only on its
already checked actual prerequisites. -/
def actualSchurResolventFamilyAfterDextV3_32 (n : ℤ)
    (p : ActualSchurEffectiveH1PairV3_30) (z : ℂ) :
    ParityPair n →L[ℂ] ParityPair n :=
  (actualFreeResolventCenterExtensionV1_30 n z).comp
    (actualComplementaryQVDJointInverseV5_30 n (z, p))

/-- The concrete fixed-factor linear map `X ↦ P V X V P` on the actual
parity-pair endomorphism algebra. -/
def actualSchurGreenSandwichMapV3_32 (n : ℤ)
    (p : ActualSchurEffectiveH1PairV3_30) :
    (ParityPair n →L[ℂ] ParityPair n) →L[ℂ]
      (ParityPair n →L[ℂ] ParityPair n) :=
  actualSchurGreenSandwichCLMMinimumV3_32 n p

/-- The actual Schur effective operator differentiated along the spectral
coordinate while the actual independent complex potential pair is fixed. -/
def actualSchurEffectiveSpectralLineV3_32 (n : ℤ)
    (p : ActualSchurEffectiveH1PairV3_30) (z : ℂ) :
    ParityPair n →L[ℂ] ParityPair n :=
  actualSchurEffectiveOperatorAfterDextV3_30 n (z, p)

end NlsGge.Schur
