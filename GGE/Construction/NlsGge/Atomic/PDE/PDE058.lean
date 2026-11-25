import Mathlib
import NlsGge.Atomic.PDE.PDE057
import NlsGge.ThirdConsultation.PDE.PDE058SupA
import NlsGge.ThirdConsultation.PDE.PDE058SupB
import NlsGge.ThirdConsultation.Common.FiniteSupport

                                                                                                                
                                                                                                                       
                                                                                
                                                                                  
                                                                                                        
                                                                                                               
                                                                        
                                                                                   
                                                                                                           
                                                                                                     
                                                                       
                                                                                                              
                                                                                                         
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

theorem actual_nls_coordinate_pairing
    (u : PhysicalSobolev38 ((3 : ℕ) : ℝ))
    (v : SobolevCarrier38 ((1 : ℕ) : ℝ))
    (hv : FiniteSupportSequence (sequenceSobolevEmbed 1 v)) :
  omegaSeq
    (carrierCoe38 ((1 : ℕ) : ℝ)
      (DPhi 1 (physicalCoreBase u) (nlsVectorField u)))
    (carrierCoe38 ((1 : ℕ) : ℝ) v) =
  fderiv ℝ (fun z : SobolevCarrier38 ((1 : ℕ) : ℝ) =>
    NlsGge.GKDefinitionDesign.transformedNLSHamiltonian z / 2)
    (birkhoffSobolev 1 (physicalCoreBase u)) v := by
  have hd := nlsHamiltonian_half_differentiableAt_core u
  have hv' := DPhi_DPhiinv (physicalCoreBase u) v
  calc omegaSeq (carrierCoe38 ((1 : ℕ) : ℝ) (DPhi 1 (physicalCoreBase u) (nlsVectorField u)))
        (carrierCoe38 ((1 : ℕ) : ℝ) v)
      = omegaSeq (carrierCoe38 ((1 : ℕ) : ℝ) (DPhi 1 (physicalCoreBase u) (nlsVectorField u)))
          (carrierCoe38 ((1 : ℕ) : ℝ) (DPhi 1 (physicalCoreBase u)
            (DPhiinv 1 (birkhoffSobolev 1 (physicalCoreBase u)) v))) := by rw [hv']
    _ = omegaPhys38 (physicalSobolevEmbed 1 (nlsVectorField u))
          (physicalSobolevEmbed 1 (DPhiinv 1 (birkhoffSobolev 1 (physicalCoreBase u)) v)) :=
        DPhi_one_symplectic _ _ _
    _ = fderiv ℝ (fun q : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
          NlsGge.GKDefinitionDesign.nlsHamiltonian q / 2) (physicalCoreBase u)
          (DPhiinv 1 (birkhoffSobolev 1 (physicalCoreBase u)) v) :=
        actual_nls_hamiltonian_normalization u _
    _ = fderiv ℝ (fun z : SobolevCarrier38 ((1 : ℕ) : ℝ) =>
          NlsGge.GKDefinitionDesign.transformedNLSHamiltonian z / 2)
          (birkhoffSobolev 1 (physicalCoreBase u)) v :=
        (transformedHam_fderiv _ v hd).symm

end NlsGge.ThirdConsultation.PDE
