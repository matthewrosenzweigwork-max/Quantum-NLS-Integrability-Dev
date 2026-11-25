import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualSchurCenterContraction38V1

                                                                                                           
                                                                                                             
                                                                                                                   
                                                                                           
                                                                                                      
                                                                                                                 
                                                                                                          
                                                                                                                  
                                                                                                            
                                                                                                             
                                                                
set_option autoImplicit false
open scoped NNReal
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur

namespace NlsGge.ThirdConsultation.S

theorem centerMap_contraction :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (n : ℤ),
      K * R ^ 3 ≤ |(n : ℝ)| → ∀ (p : SchurPair), ‖p‖ ≤ R →
      Set.MapsTo (centerMapAt n p)
        (Metric.closedBall (spectralCenter n) (1 / 2))
        (Metric.ball (spectralCenter n) (1 / 2)) ∧
      LipschitzOnWith (1 / 4 : ℝ≥0) (centerMapAt n p)
        (Metric.closedBall (spectralCenter n) (1 / 2)) := by
  refine ⟨max actualSchurCenterThresholdConstant38 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro R hR n hK p hp
  have hR0 : 0 ≤ R ^ 3 := pow_nonneg (by linarith) 3
  have hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hR0) hK
  have hpm : max ‖p.1‖ ‖p.2‖ ≤ R := (le_of_eq (Prod.norm_def p).symm).trans hp
  have hp1 : ‖p.1‖ ≤ R := le_trans (le_max_left _ _) hpm
  have hp2 : ‖p.2‖ ≤ R := le_trans (le_max_right _ _) hpm
  obtain ⟨hmaps, hlip⟩ :=
    NlsGge.Schur.actualSchurCenterMap38_mapsTo_and_lipschitz R hR n hthr p hp1 hp2
  refine ⟨?_, ?_⟩
  · intro w hw
    have ew : centerMapAt n p w = spectralCenter n + actualSchurAlpha38 n p w := rfl
    rw [Metric.mem_ball, dist_eq_norm, ew]
    linarith [hmaps w hw]
  · refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have ex : centerMapAt n p x = spectralCenter n + actualSchurAlpha38 n p x := rfl
    have ey : centerMapAt n p y = spectralCenter n + actualSchurAlpha38 n p y := rfl
    have hcoe : ((1 / 4 : ℝ≥0) : ℝ) = 1 / 4 := by norm_num
    rw [dist_eq_norm, dist_eq_norm, ex, ey, hcoe]
    have e : spectralCenter n + actualSchurAlpha38 n p x - (spectralCenter n + actualSchurAlpha38 n p y) =
        actualSchurAlpha38 n p x - actualSchurAlpha38 n p y := by ring
    rw [e]
    exact hlip x hx y hy

end NlsGge.ThirdConsultation.S
