import Mathlib
import NlsGge.Atomic.M.M051Host
import NlsGge.ThirdConsultation.KSPS.KSPS031Sharp
import NlsGge.ThirdConsultation.KSPS.KSPS031SharpLaurentCore
import NlsGge.ThirdConsultation.M.M016LittleO

                                                                                                         
                                                                                                                       
                                                                                                        
                                                                             
                                                                                                     
                                                                                                           
                                                                               
                                                                                                               
                                                                                               
                                                                                                                
                                                                                                              
                                                  
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS031SL
noncomputable section

theorem sharp_littleO_along_halfNodes (N : ℕ) (hN : 1 ≤ N) (φ : KSPS.SobolevC N) (F : ℂ → ℂ)
    (hinf : NlsGge.ThirdConsultation.M.AnalyticAtInfinity (fun z : ℂ => F z + Complex.I * z))
    (hhalf : ∃ J : ℕ, ∀ (j : ℤ) (hj : J ≤ j.natAbs),
      ∃ hchart : KSPSWKB.NonresonantBranchDomain φ j (KSPSWKB.halfNode j),
        F (KSPSWKB.halfNode j) = KSPSWKB.primitive N φ ⟨(j, KSPSWKB.halfNode j), hchart⟩) :
    ∀ K : ℕ, K ≤ N + 1 → ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      ‖F z + Complex.I * z - ∑ k ∈ Finset.Icc 1 K,
          KSPS.integralRiccatiLeft φ k / (2 * Complex.I * z) ^ k‖ ≤ C / ‖z‖ ^ (K + 1) := by
  obtain ⟨J₁, hF⟩ := hhalf
  obtain ⟨J, hchart, hsharp⟩ := KSPS.nonresonant_WKB_coefficients_sharp N hN φ
  obtain ⟨hw0, hwt⟩ := halfNode_inv_seq (max J J₁)
  have hgA : AnalyticAt ℂ
      (fun w : ℂ => if w = 0 then 0 else (fun z : ℂ => F z + Complex.I * z) w⁻¹) 0 := hinf
  have ho : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ‖(fun w : ℂ => if w = 0 then 0 else (fun z : ℂ => F z + Complex.I * z) w⁻¹)
          ((((((n : ℤ) + ((max J J₁ : ℕ) : ℤ) : ℤ) : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ))⁻¹) -
        ∑ k ∈ Finset.range (N + 1 + 1),
          (if k = 0 then 0 else KSPS.integralRiccatiLeft φ k / (2 * Complex.I) ^ k) *
            ((((((n : ℤ) + ((max J J₁ : ℕ) : ℤ) : ℤ) : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ))⁻¹) ^ k‖ ≤
        ε * ‖((((((n : ℤ) + ((max J J₁ : ℕ) : ℤ) : ℤ) : ℂ) + (1 / 2 : ℂ)) *
          (Real.pi : ℂ))⁻¹)‖ ^ (N + 1) := by
    intro ε hε
    obtain ⟨J', hJ'⟩ := hsharp ε hε
    filter_upwards [eventually_ge_atTop J'] with n hn
    have hnat : ((n : ℤ) + ((max J J₁ : ℕ) : ℤ)).natAbs = n + max J J₁ := by
      have e : ((n : ℤ) + ((max J J₁ : ℕ) : ℤ)) = ((n + max J J₁ : ℕ) : ℤ) := by push_cast; ring
      rw [e, Int.natAbs_natCast]
    have hjJ' : J' ≤ ((n : ℤ) + ((max J J₁ : ℕ) : ℤ)).natAbs := by rw [hnat]; omega
    have hjJ : J ≤ ((n : ℤ) + ((max J J₁ : ℕ) : ℤ)).natAbs := by
      rw [hnat]; have := le_max_left J J₁; omega
    have hjJ₁ : J₁ ≤ ((n : ℤ) + ((max J J₁ : ℕ) : ℤ)).natAbs := by
      rw [hnat]; have := le_max_right J J₁; omega
    obtain ⟨hc1, hFx⟩ := hF ((n : ℤ) + ((max J J₁ : ℕ) : ℤ)) hjJ₁
    have hb := hJ' ((n : ℤ) + ((max J J₁ : ℕ) : ℤ)) hjJ' hjJ
    have hx : KSPSWKB.halfNode ((n : ℤ) + ((max J J₁ : ℕ) : ℤ)) ≠ 0 := by
      intro h
      have h1 := NlsGge.ThirdConsultation.KSPS031Analytic.one_le_norm_halfNode_expr
        ((n : ℤ) + ((max J J₁ : ℕ) : ℤ))
      have h2 : ‖KSPSWKB.halfNode ((n : ℤ) + ((max J J₁ : ℕ) : ℤ))‖ = 0 := by rw [h, norm_zero]
      have h3 : (1 : ℝ) ≤ ‖KSPSWKB.halfNode ((n : ℤ) + ((max J J₁ : ℕ) : ℤ))‖ := h1
      linarith
    have hexpr := sharp_expr_eq N (fun k => KSPS.integralRiccatiLeft φ k)
      (KSPSWKB.halfNode ((n : ℤ) + ((max J J₁ : ℕ) : ℤ)))
      (KSPSWKB.primitive N φ ⟨(((n : ℤ) + ((max J J₁ : ℕ) : ℤ)),
        KSPSWKB.halfNode ((n : ℤ) + ((max J J₁ : ℕ) : ℤ))), hc1⟩) hx
    have key : (fun w : ℂ => if w = 0 then 0 else (fun z : ℂ => F z + Complex.I * z) w⁻¹)
          (KSPSWKB.halfNode ((n : ℤ) + ((max J J₁ : ℕ) : ℤ)))⁻¹ -
        ∑ k ∈ Finset.range (N + 1 + 1),
          (if k = 0 then 0 else KSPS.integralRiccatiLeft φ k / (2 * Complex.I) ^ k) *
            (KSPSWKB.halfNode ((n : ℤ) + ((max J J₁ : ℕ) : ℤ)))⁻¹ ^ k =
        KSPSWKB.primitive N φ ⟨(((n : ℤ) + ((max J J₁ : ℕ) : ℤ)),
            KSPSWKB.halfNode ((n : ℤ) + ((max J J₁ : ℕ) : ℤ))), hc1⟩ +
          Complex.I * (KSPS.wkbPhase φ (KSPSWKB.halfNode ((n : ℤ) + ((max J J₁ : ℕ) : ℤ))) +
            Complex.I * (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) *
              KSPS.integralRiccatiLeft φ (N + 1) *
              KSPSWKB.halfNode ((n : ℤ) + ((max J J₁ : ℕ) : ℤ)) ^ (-((N + 1 : ℕ) : ℤ))) := by
      simp only [inv_eq_zero, hx, if_false, inv_inv]
      rw [hFx]
      unfold KSPS.wkbPhase
      exact hexpr.symm
    have hgoal : ‖KSPSWKB.primitive N φ ⟨(((n : ℤ) + ((max J J₁ : ℕ) : ℤ)),
            KSPSWKB.halfNode ((n : ℤ) + ((max J J₁ : ℕ) : ℤ))), hc1⟩ +
          Complex.I * (KSPS.wkbPhase φ (KSPSWKB.halfNode ((n : ℤ) + ((max J J₁ : ℕ) : ℤ))) +
            Complex.I * (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) *
              KSPS.integralRiccatiLeft φ (N + 1) *
              KSPSWKB.halfNode ((n : ℤ) + ((max J J₁ : ℕ) : ℤ)) ^ (-((N + 1 : ℕ) : ℤ)))‖ ≤
        ε * ‖(KSPSWKB.halfNode ((n : ℤ) + ((max J J₁ : ℕ) : ℤ)))⁻¹‖ ^ (N + 1) := by
      rw [norm_inv, inv_pow, ← div_eq_mul_inv]
      exact hb
    rw [← key] at hgoal
    exact hgoal
  have hcm := NlsGge.ThirdConsultation.M016CL.coeff_match_littleO
    (fun w : ℂ => if w = 0 then 0 else (fun z : ℂ => F z + Complex.I * z) w⁻¹) hgA
    (fun k => if k = 0 then 0 else KSPS.integralRiccatiLeft φ k / (2 * Complex.I) ^ k) (N + 1)
    (fun n : ℕ => ((((((n : ℤ) + ((max J J₁ : ℕ) : ℤ) : ℤ) : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ))⁻¹))
    hw0 hwt ho
  obtain ⟨C', r, hC', hr, hdisc⟩ := hcm.1
  exact exterior_of_disc (fun z : ℂ => F z + Complex.I * z) (fun k => KSPS.integralRiccatiLeft φ k)
    (N + 1) C' r hC' hr hdisc

end
end NlsGge.ThirdConsultation.KSPS031SL
