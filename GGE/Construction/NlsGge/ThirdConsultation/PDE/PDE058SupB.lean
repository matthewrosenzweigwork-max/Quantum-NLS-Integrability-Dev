import Mathlib
import NlsGge.ThirdConsultation.PDE.PDE058SupGen
import NlsGge.ThirdConsultation.PDE.Round14Deriv
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.Atomic.G6.G6027
import NlsGge.Atomic.G6.G6033Host
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.Birkhoff.S01Translation38

                                                                               
                                                                                                                       
                                                       
                                                                                                                   
                                                                                   
                                                                                                             
                                                                                                                         
                                                                                                  
                                                                                                                            
                                                                                                              
                                                                                                              
                                                                                          
                                                                                                     
                                                                                                                 
                                                                        
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.PDE

theorem birkhoffSobolev_one_eq_TC :
    birkhoffSobolev 1 = fun p : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
      actualBirkhoffTop38.TC 1
        ((physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).toContinuousLinearEquiv p) := by
  funext p
  rw [actualBirkhoffTop38_TC]
  show birkhoffSobolev 1 p = birkhoffSobolev 1 ((physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm
    (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) p))
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem DPhi_one_symplectic (p h k : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    omegaSeq (carrierCoe38 ((1 : ℕ) : ℝ) (DPhi 1 p h)) (carrierCoe38 ((1 : ℕ) : ℝ) (DPhi 1 p k)) =
      omegaPhys38 (physicalSobolevEmbed 1 h) (physicalSobolevEmbed 1 k) := by
  unfold omegaSeq DPhi
  rw [birkhoffSobolev_one_eq_TC,
    TC_one_comp_symplectic actualBirkhoffTop38 (actualBirkhoffAnalytic38.mono (Set.subset_univ _))
      actualBirkhoffCanonical38 (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).toContinuousLinearEquiv p h k,
    ← stdSymplectic38_fourierSeq38]
  congr 1 <;> funext n <;> exact (physicalSobolevEmbed_fourier 1 _ n).symm

theorem DPhi_DPhiinv (p : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (v : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    DPhi 1 p (DPhiinv 1 (birkhoffSobolev 1 p) v) = v := by
  obtain ⟨hΦa, hΨa, hL, hR, -, -⟩ := G6027 1 le_rfl
  exact fderiv_apply_fderiv_rightInverse (birkhoffSobolev 1) (inverseBirkhoffSobolev 1) hR hL p
    (hΦa p (Set.mem_univ _)).differentiableAt (hΨa _ (Set.mem_univ _)).differentiableAt v

theorem transformedHam_fderiv (p : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (v : SobolevCarrier38 ((1 : ℕ) : ℝ))
    (hd : DifferentiableAt ℝ (fun q : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
      NlsGge.GKDefinitionDesign.nlsHamiltonian q / 2) p) :
    fderiv ℝ (fun z : SobolevCarrier38 ((1 : ℕ) : ℝ) =>
        NlsGge.GKDefinitionDesign.transformedNLSHamiltonian z / 2) (birkhoffSobolev 1 p) v =
      fderiv ℝ (fun q : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
        NlsGge.GKDefinitionDesign.nlsHamiltonian q / 2) p (DPhiinv 1 (birkhoffSobolev 1 p) v) := by
  obtain ⟨-, hΨa, hL, -, -, -⟩ := G6027 1 le_rfl
  have hfun : (fun z : SobolevCarrier38 ((1 : ℕ) : ℝ) =>
      NlsGge.GKDefinitionDesign.transformedNLSHamiltonian z / 2) =
      fun z => (fun q : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
        NlsGge.GKDefinitionDesign.nlsHamiltonian q / 2) (inverseBirkhoffSobolev 1 z) := rfl
  rw [hfun]
  exact fderiv_comp_leftInverse_apply (fun q : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
      NlsGge.GKDefinitionDesign.nlsHamiltonian q / 2) (birkhoffSobolev 1) (inverseBirkhoffSobolev 1) hL p hd
    (hΨa _ (Set.mem_univ _)).differentiableAt v

end NlsGge.ThirdConsultation.PDE
