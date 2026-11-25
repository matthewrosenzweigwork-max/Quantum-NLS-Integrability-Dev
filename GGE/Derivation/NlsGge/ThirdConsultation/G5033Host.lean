import Mathlib
import NlsGge.GK38.Defs
import NlsGge.GK38.AbelianSpace
import NlsGge.GK38.Lib.EntireProductsParama
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import Armstrong.Work.ActualCartesianXYModels

/- G5-033 HOST (proof development, AUTHOR; not self-reviewed). Hosts the design names the G5-033 head needs and that
   no existing NlsGge/ module defines (grep of NlsGge/, Armstrong/ and the round-4 worker folders, 2026-10-31):
   pairGradientCLM, pairPoissonCLM, cartesianX, cartesianY, angleDerivative, psiRootAt.
   Bodies are byte-identical extractions from the Pro design files:
   pairGradientCLM and pairPoissonCLM and angleDerivative and psiRootAt from DEFINITIONS/G5.lean.md
   (lines 21-26, 31-32, 85-89, 118-119); cartesianX and cartesianY from DEFINITIONS/G4.lean.md (lines 105-109).
   psiAt is NOT hosted here: it is landed in NlsGge/Atomic/G5/G5024.lean (NlsGge.GKDefinitionDesign.psiAt).
   cartesianX/Y realize through Armstrong/Work/ActualCartesianXYModels.lean (root option-1 approved set). -/
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- The bilinear, not Hermitian, L2 gradient of a complex functional. -/
def pairGradientCLM (L : PotPair →L[ℂ] ℂ) : PotPair :=
  (star ((InnerProductSpace.toDual ℂ PhysicalL2).symm
      (L.comp (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2))),
   star ((InnerProductSpace.toDual ℂ PhysicalL2).symm
      (L.comp (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2))))

def pairPoissonCLM (L M : PotPair →L[ℂ] ℂ) : ℂ :=
  L (-Complex.I • (pairGradientCLM M).2, Complex.I • (pairGradientCLM M).1)

def cartesianX (n : ℤ) : PotPair → ℂ :=
  gk16ScalarXModel38 sourceF betaSum n

def cartesianY (n : ℤ) : PotPair → ℂ :=
  gk16ScalarYModel38 sourceF betaSum n

/-- Global differential of the local angle, only used where the radius is nonzero. -/
def angleDerivative (n : ℤ) (φ : PotPair) : PotPair →L[ℂ] ℂ :=
  (cartesianX n φ ^ 2 + cartesianY n φ ^ 2)⁻¹ •
    (cartesianX n φ • fderiv ℂ (cartesianY n) φ -
      cartesianY n φ • fderiv ℂ (cartesianX n) φ)

def psiRootAt (n m : ℤ) (φ : PotPair) : ℂ :=
  Lib.sigmaOf (p2Extend38 n (sourceF n φ)) m

end
end NlsGge.GKDefinitionDesign
