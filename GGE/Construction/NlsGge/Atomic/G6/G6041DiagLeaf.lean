import Mathlib
import NlsGge.Atomic.G6.G6033
import NlsGge.Atomic.G6.G6035Core
import NlsGge.Atomic.G6.G6036Host

                                                                                                                   
                                                                                               
                                                                                                             
                                                                                                               
                                                                                                                         
                                                                                                                         
                                                                                                                   
                                                                                                
                                                                                                          
                                                                                                     
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem diagonalHamiltonian_eq_actionHamiltonian
    (I : PositiveActionSpace) (x : RealDiagonalSpace)
    (hx : ∀ n : ℤ, (x n)^2 = I.val n) :
  diagonalHamiltonian x = actionHamiltonian I := by
  unfold diagonalHamiltonian actionHamiltonian
  refine G6033.2 _ _ (fun n => ?_)
  rw [NlsGge.ThirdConsultation.G6035S.norm_coe_root_sq]
  have hw : 0 < actionWeight n := NlsGge.ThirdConsultation.G6035S.w_pos n
  have hc : carrierCoe38 ((1 : ℕ) : ℝ) (diagonalToSobolev x) n =
      diagonalPhase * ((x n / Real.sqrt (actionWeight n) : ℝ) : ℂ) := by
    unfold diagonalToSobolev
    rw [carrierCoe38_mk]
  have hph : ‖diagonalPhase‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, diagonalPhase, map_div₀, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Complex.normSq_apply]
    simp
  rw [hc, norm_mul, mul_pow, hph, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt hw.le, hx n]
  rfl

end
end NlsGge.GKDefinitionDesign
