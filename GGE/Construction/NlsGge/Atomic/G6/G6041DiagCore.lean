import Mathlib
import NlsGge.Atomic.G6.G6036Core
import NlsGge.ThirdConsultation.G6.Energy031A

                                                                                       
                                                                                                             
                                                                                                                
                                                                  
                                                                                                                   
                                                                              
                                                                                                                   
                                                                                                 
                                                                                            
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6041S
noncomputable section

theorem phase_norm_sq' : ‖diagonalPhase‖ ^ 2 = 1 := by
  rw [← Complex.normSq_eq_norm_sq, diagonalPhase, map_div₀, Complex.normSq_ofReal,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Complex.normSq_apply]
  simp

theorem diag_coord_sq (x : RealDiagonalSpace) (n : ℤ) :
    sobolevModeWeight ((1 : ℕ) : ℝ) n * ‖carrierCoe38 ((1 : ℕ) : ℝ) (diagonalToSobolev x) n‖ ^ 2 = x n ^ 2 := by
  have hw : 0 < actionWeight n := sobolevModeWeight_pos 1 n
  have e : sobolevModeWeight ((1 : ℕ) : ℝ) n = actionWeight n := by rw [Nat.cast_one]; rfl
  rw [NlsGge.ThirdConsultation.G6036S.coe_diag, e, norm_mul, mul_pow, phase_norm_sq', one_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hw.le]
  field_simp

theorem norm_diagonalToSobolev (x : RealDiagonalSpace) : ‖diagonalToSobolev x‖ = ‖x‖ := by
  have h1 := carrier_hasSum_norm_sq38 ((1 : ℕ) : ℝ) (diagonalToSobolev x)
  simp only [diag_coord_sq] at h1
  have h2 := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.unique h2)

def diagCLM : RealDiagonalSpace →L[ℝ] SobolevCarrier38 ((1 : ℕ) : ℝ) :=
  LinearMap.mkContinuous
    { toFun := diagonalToSobolev
      map_add' := fun x y => by
        apply carrierExt38; funext n
        rw [carrierCoe38_add, NlsGge.ThirdConsultation.G6036S.coe_diag, NlsGge.ThirdConsultation.G6036S.coe_diag,
          NlsGge.ThirdConsultation.G6036S.coe_diag, lp.coeFn_add, Pi.add_apply]
        push_cast; ring
      map_smul' := fun a x => by
        apply carrierExt38; funext n
        rw [RingHom.id_apply, carrierCoe38_smul, NlsGge.ThirdConsultation.G6036S.coe_diag,
          NlsGge.ThirdConsultation.G6036S.coe_diag, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        push_cast; ring }
    1 (fun x => by rw [one_mul]; exact (norm_diagonalToSobolev x).le)

theorem diagCLM_apply (x : RealDiagonalSpace) : diagCLM x = diagonalToSobolev x := rfl

theorem diagonalHamiltonian_analytic_of
    (h31A : AnalyticOnNhd ℝ nlsHamiltonian Set.univ)
    (hinvA : AnalyticOnNhd ℝ (inverseBirkhoffSobolev 1) Set.univ) :
    AnalyticOnNhd ℝ diagonalHamiltonian Set.univ := by
  intro x _
  have he : diagonalHamiltonian = fun y => nlsHamiltonian (inverseBirkhoffSobolev 1 (diagCLM y)) := rfl
  rw [he]
  have h1 : AnalyticAt ℝ (fun y => inverseBirkhoffSobolev 1 (diagCLM y)) x :=
    (hinvA _ (Set.mem_univ _)).comp (diagCLM.analyticAt x)
  exact (h31A _ (Set.mem_univ _)).comp h1

end
end NlsGge.ThirdConsultation.G6041S
