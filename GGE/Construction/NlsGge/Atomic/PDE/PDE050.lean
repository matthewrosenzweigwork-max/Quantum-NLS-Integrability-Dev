                                                                                                                                        
import NlsGge.Birkhoff.S01Translation38

                                                                           
                                                                                                                       
                                                                                                                             
                                                                                               

set_option autoImplicit false
open NlsGge.Birkhoff NlsGge.Pilot

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

theorem translation_momentum_hamiltonian {u ux v : PhysicalL2}
    (hw : IsFourierDeriv38 u ux) (hv : SobolevSquareSummable 1 (physicalFourier v)) :
    HasDerivAt (fun s : ℝ => -(momentumFourier38 (u + s • v)) / 2) (omegaPhys38 ux v) 0 := by
  have h := hasDerivAt_neg_half_momentum_line38 hw v hv
  have hfun : (fun s : ℝ => -(momentumFourier38 (u + s • v)) / 2) =
      fun s : ℝ => -(momentumFourier38 (u + (s : ℂ) • v)) / 2 := by
    funext s
    exact congrArg (fun x => -(momentumFourier38 (u + x)) / 2)
      (RCLike.real_smul_eq_coe_smul (K := ℂ) s v)
  rw [hfun]
  exact h

end
end NlsGge.ThirdConsultation.PDE
