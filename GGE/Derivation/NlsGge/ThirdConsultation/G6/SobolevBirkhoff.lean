import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.G6.BirkhoffBasic

/- G6SBH host (proof development, AUTHOR; not reviewed).  Target NlsGge/ThirdConsultation/G6/SobolevBirkhoff.lean.
   Pro round 15 Q6 section 3 (PRO_DEFINITION_RESPONSE_FP80_15.md, request pin cc702018): the four literal G6 Sobolev
   bodies physicalSobolevRecover, birkhoffSobolev, inverseBirkhoffSobolev, sobolevJacobianConjugate, VERBATIM (same bodies
   as followup13 DEFINITIONS/G6.lean.md).  sequenceSobolevEmbed / physicalSobolevEmbed are IMPORTED from
   Sobolev.Round5 (not redeclared); physicalBirkhoff / physicalInverseBirkhoff from G6.BirkhoffBasic.  No analyticity,
   no completed Birkhoff input.  The `else 0` branches are shown unused by the SobolevBirkhoffCompat leaves. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

def physicalSobolevRecover (m : ℕ) (u : PhysicalL2) :
    PhysicalSobolev38 (m : ℝ) :=
  if h : fourierSeq38 u ∈ seqSobolev38 (m : ℝ) then
    (physicalSobolevFourierEquiv38 (m : ℝ)).symm
      (carrierMk38 (m : ℝ) (fourierSeq38 u) h)
  else 0

def birkhoffSobolev (m : ℕ)
    (u : PhysicalSobolev38 (m : ℝ)) :
    SobolevCarrier38 (m : ℝ) :=
  let z : ℤ → ℂ := physicalBirkhoff (physicalSobolevEmbed m u)
  if h : z ∈ seqSobolev38 (m : ℝ) then
    carrierMk38 (m : ℝ) z h
  else 0

def inverseBirkhoffSobolev (m : ℕ)
    (z : SobolevCarrier38 (m : ℝ)) :
    PhysicalSobolev38 (m : ℝ) :=
  physicalSobolevRecover m
    (physicalInverseBirkhoff (sequenceSobolevEmbed m z))

def sobolevJacobianConjugate (m : ℕ)
    (u : PhysicalSobolev38 (m : ℝ)) :
    PhysicalSobolev38 (m : ℝ) →L[ℝ] PhysicalSobolev38 (m : ℝ) :=
  (physicalSobolevFourierEquiv38 (m : ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fderiv ℝ (birkhoffSobolev m) u)

end NlsGge.GKDefinitionDesign

end
