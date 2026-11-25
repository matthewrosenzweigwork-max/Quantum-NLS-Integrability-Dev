import Mathlib
import NlsGge.ThirdConsultation.KST.KST066Host
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.ThirdConsultation.Sobolev.Round5

/- KSN021Host HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/KSN/KSN021Host.lean. SUPPORTING host module (no packet increment). Bodies VERBATIM from followup13
   DEFINITIONS/KSN.lean.md L341-360 (section "Real restrictions at arbitrary exponents", namespace
   NlsGge.GKDefinitionDesign): physicalSobolevRecoverRealExponent, inverseBirkhoffSobolevRealExponent, inverseSmoothing —
   the three names of that block NOT hosted by proof development's KSN022Host (which hosts birkhoffSobolevRealExponent only).
   grep NlsGge/ (2026-11-03): none of the three is declared. Consumers: KSN-021 (inverseSmoothing), KSN-023/025
   (inverseBirkhoffSobolevRealExponent). Opens as KSN022Host (the dependent `if` needs classical decidability).
   The design block's `fractional_constructor_integer_compatibility` is a theorem obligation, not hosted here.
   Needs ROOT MAIN PROBE (KST066Host, BirkhoffBasic, Sobolev.Round5 absent from mirror). -/
set_option autoImplicit false
noncomputable section
open scoped Classical
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

def physicalSobolevRecoverRealExponent (s : ℝ) (u : PhysicalL2) : PhysicalSobolev38 s :=
  if h : fourierSeq38 u ∈ seqSobolev38 s then
    (physicalSobolevFourierEquiv38 s).symm (carrierMk38 s (fourierSeq38 u) h)
  else 0

def inverseBirkhoffSobolevRealExponent (s : ℝ) (hs : 0 ≤ s) (z : SobolevCarrier38 s) :
    PhysicalSobolev38 s :=
  physicalSobolevRecoverRealExponent s
    (physicalInverseBirkhoff (sequenceSobolevEmbedRealExponent s hs z))

def inverseSmoothing (N : ℕ) (z : SobolevCarrier38 (N : ℝ)) :
    PhysicalSobolev38 ((N : ℝ) + 1) :=
  physicalSobolevRecoverRealExponent ((N : ℝ) + 1)
    (physicalInverseBirkhoff (sequenceSobolevEmbed N z) -
      reflectedFourierL2.symm (sequenceSobolevEmbed N z))

end NlsGge.GKDefinitionDesign

end
