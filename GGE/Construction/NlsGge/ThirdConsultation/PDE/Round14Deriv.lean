import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff

                                                                                  
                                                                                                                     
                                                                                                                             
                                                                                                                           
                                                                                                                   
                                                                                                    
                                                                                              
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
