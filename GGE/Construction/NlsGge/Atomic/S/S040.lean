import NlsGge.Schur.ActualSchurBallMapJacobian38V1
import NlsGge.Atomic.S.S039

                                                                                                                                                                                                                                                                                                                                                                                                                      
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem schurBallMap_det_mem_Icc (M N : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : schurCommonThreshold * R ^ 6 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : z ∈ schurH1Ball N R) :
    schurRealJacobianDet M N z ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  obtain ⟨h1, h2⟩ := schurCommonThreshold_hyps R hR M hM
  exact actualSchurBallMap38_det_mem_Icc N M R hR h1 h2 z hz

end NlsGge.ThirdConsultation.S
