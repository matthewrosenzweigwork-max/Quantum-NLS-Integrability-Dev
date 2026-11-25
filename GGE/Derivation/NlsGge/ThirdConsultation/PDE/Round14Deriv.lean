import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff

/- PDEDERIV HOST PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target
   NlsGge/ThirdConsultation/PDE/Round14Deriv.lean, namespace NlsGge.ThirdConsultation.PDE (root/integrator to place).
   Bodies VERBATIM from PRO_DEFINITION_RESPONSE_FP80_14.md, shared PDE block (l.2639 ff., "This block replaces the historical
   nlsVectorField/DT0/... block"): DPhi, DPhiinv, omegaSeq, DT0. physicalCoreFourier/physicalCoreBase/nlsVectorField of the
   same block are already hosted in Round14Field.lean (whose header defers DPhi/DPhiinv to a separate install); not
   re-declared. Consumers: PDE-054 (DT0), PDE-058/062 (DPhi, omegaSeq), later PDE packets (DPhiinv).
   Lexical repair (as in Round14Field): opens reduced to namespaces present in the closure. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GKDefinitionDesign NlsGge.Atomic.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

def DPhi (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) :
    PhysicalSobolev38 (m : ℝ) →L[ℝ] SobolevCarrier38 (m : ℝ) :=
  fderiv ℝ (birkhoffSobolev m) u

def DPhiinv (m : ℕ) (z : SobolevCarrier38 (m : ℝ)) :
    SobolevCarrier38 (m : ℝ) →L[ℝ] PhysicalSobolev38 (m : ℝ) :=
  fderiv ℝ (inverseBirkhoffSobolev m) z

def omegaSeq (x y : ℤ → ℂ) : ℝ := stdSymplectic38 x y

def DT0 (x : SobolevCarrier38 ((0 : ℕ) : ℝ)) :
    SobolevCarrier38 ((0 : ℕ) : ℝ) →L[ℝ]
      SobolevCarrier38 ((0 : ℕ) : ℝ) :=
  fderiv ℝ (NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38.TC 0) x

end
end NlsGge.ThirdConsultation.PDE
