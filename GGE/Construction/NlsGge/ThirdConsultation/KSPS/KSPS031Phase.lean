import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS031Host
import NlsGge.ThirdConsultation.KSPS.KSPS031Analytic

                                                                                             
                                                                                                      
                                                                                                     
                                                                                                       
                                                                                                            
                                                                                                   
                                                                            
set_option autoImplicit false
open scoped BigOperators
open NlsGge.ThirdConsultation.KSPSRiccati

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem wkbPhase_halfNode_tail
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) :
    ∃ (C : ℝ) (J : ℕ), 0 ≤ C ∧
      ∀ j : ℤ, J ≤ j.natAbs →
        ‖wkbPhase φ (KSPSWKB.halfNode j) - KSPSWKB.halfNode j‖ ≤
          C / ‖KSPSWKB.halfNode j‖ := by
  refine ⟨∑ k ∈ Finset.Icc 1 N, ‖integralRiccatiLeft φ k‖, 0,
    Finset.sum_nonneg (fun k _ => norm_nonneg _), fun j _ => ?_⟩
  have h1 : 1 ≤ ‖KSPSWKB.halfNode j‖ :=
    NlsGge.ThirdConsultation.KSPS031Analytic.one_le_norm_halfNode_expr j
  have e : wkbPhase φ (KSPSWKB.halfNode j) - KSPSWKB.halfNode j =
      Complex.I * ∑ k ∈ Finset.Icc 1 N,
        (2 * Complex.I * KSPSWKB.halfNode j) ^ (-(k : ℤ)) * integralRiccatiLeft φ k := by
    unfold wkbPhase
    ring
  rw [e, norm_mul, Complex.norm_I, one_mul]
  exact NlsGge.ThirdConsultation.KSPS031Analytic.finite_laurent_sum_tail_bound
    (fun k => integralRiccatiLeft φ k) (KSPSWKB.halfNode j) h1

theorem primitive_chart_error_of_phase
    (N : ℕ) (φ : SobolevC N) (j : ℤ) (θ : ℂ)
    (hchart : KSPSWKB.NonresonantBranchDomain φ j
      (KSPSWKB.halfNode j))
    (hθ : ‖θ - KSPSWKB.halfNode j‖ < Real.pi / 8) :
    ‖KSPSWKB.primitive N φ
        ⟨(j, KSPSWKB.halfNode j), hchart⟩ + Complex.I * θ‖ ≤
      2 * ‖discriminant φ (KSPSWKB.halfNode j) -
        2 * Complex.cos θ‖ := by
  have hD : ‖discriminant φ (KSPSWKB.halfNode j) / 2‖ < 1 / 2 := And.right hchart
  exact NlsGge.ThirdConsultation.KSPS031Analytic.chart_core j
    (discriminant φ (KSPSWKB.halfNode j)) θ hD hθ

end
end NlsGge.ThirdConsultation.KSPS
