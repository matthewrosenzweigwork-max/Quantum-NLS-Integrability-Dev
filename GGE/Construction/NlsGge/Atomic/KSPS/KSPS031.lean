import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS031Strip
import NlsGge.ThirdConsultation.KSPS.KSPS031Phase

                                                                                           
                                                                                                           
                                                                                                                 
                                                                                                              
                                                                                                     
                                                                                                                 
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem nonresonant_WKB_coefficients
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) :
    ∃ (C : ℝ) (J : ℕ), 0 ≤ C ∧
      ∀ j : ℤ, J ≤ j.natAbs →
        ∃ hchart : KSPSWKB.NonresonantBranchDomain φ j
            (KSPSWKB.halfNode j),
          (1 / 2 : ℝ) ≤
            ‖Complex.sin (wkbPhase φ (KSPSWKB.halfNode j))‖ ∧
          ‖discriminant φ (KSPSWKB.halfNode j) -
              2 * Complex.cos (wkbPhase φ (KSPSWKB.halfNode j))‖ ≤
            C / ‖KSPSWKB.halfNode j‖ ^ N ∧
          ‖KSPSWKB.primitive N φ
                ⟨(j, KSPSWKB.halfNode j), hchart⟩ +
              Complex.I * wkbPhase φ (KSPSWKB.halfNode j)‖ ≤
            C / ‖KSPSWKB.halfNode j‖ ^ N := by
  obtain ⟨CΔ, L, hCΔ, hL, hstrip⟩ := discriminant_wkb_strip_bound N hN φ 0 le_rfl
  obtain ⟨Cφ, J0, hCφ, htail⟩ := wkbPhase_halfNode_tail N hN φ
  obtain ⟨J1, hJ1⟩ := NlsGge.ThirdConsultation.KSPS031Analytic.halfNode_threshold L (8 * Cφ) (2 * CΔ)
  refine ⟨2 * CΔ, max J0 J1, by linarith, fun j hj => ?_⟩
  have hj0 : J0 ≤ j.natAbs := (le_max_left _ _).trans hj
  have hj1 : J1 ≤ j.natAbs := (le_max_right _ _).trans hj
  obtain ⟨hXL, hXφ, hXΔ⟩ := hJ1 j hj1
  have hXL' : L ≤ ‖KSPSWKB.halfNode j‖ := hXL
  have hXφ' : 8 * Cφ ≤ ‖KSPSWKB.halfNode j‖ := hXφ
  have hXΔ' : 2 * CΔ ≤ ‖KSPSWKB.halfNode j‖ := hXΔ
  have hX1 : 1 ≤ ‖KSPSWKB.halfNode j‖ :=
    NlsGge.ThirdConsultation.KSPS031Analytic.one_le_norm_halfNode_expr j
  have hX0 : 0 < ‖KSPSWKB.halfNode j‖ := by linarith
  have hreal : KSPSWKB.halfNode j = ((((j : ℝ) + 1 / 2) * Real.pi : ℝ) : ℂ) := by
    unfold KSPSWKB.halfNode
    push_cast
    ring
  have him : |(KSPSWKB.halfNode j).im| ≤ 0 := by
    rw [hreal, Complex.ofReal_im, abs_zero]
  have hE := hstrip (KSPSWKB.halfNode j) hXL' him
  have hEΔ : CΔ / ‖KSPSWKB.halfNode j‖ ^ N ≤ 1 / 2 :=
    NlsGge.ThirdConsultation.KSPS031Analytic.div_pow_le_of_le N hN hX1 hXΔ'
  have hph : ‖wkbPhase φ (KSPSWKB.halfNode j) - KSPSWKB.halfNode j‖ ≤ 1 / 8 := by
    refine (htail j hj0).trans
      (NlsGge.ThirdConsultation.KSPS031Analytic.div_le_of_mul_le_self (1 / 8) hX0 (by norm_num) ?_)
    have e : Cφ / (1 / 8) = 8 * Cφ := by ring
    rw [e]
    exact hXφ'
  obtain ⟨hsin, hdisc⟩ := NlsGge.ThirdConsultation.KSPS031Analytic.halfNode_phase_consequences j
    (wkbPhase φ (KSPSWKB.halfNode j)) (discriminant φ (KSPSWKB.halfNode j))
    (CΔ / ‖KSPSWKB.halfNode j‖ ^ N) hph hE hEΔ
  have hchart : KSPSWKB.NonresonantBranchDomain φ j (KSPSWKB.halfNode j) := by
    unfold KSPSWKB.NonresonantBranchDomain
    refine ⟨?_, hdisc⟩
    rw [sub_self, norm_zero]
    positivity
  have hθ : ‖wkbPhase φ (KSPSWKB.halfNode j) - KSPSWKB.halfNode j‖ < Real.pi / 8 := by
    linarith [Real.pi_gt_three]
  refine ⟨hchart, hsin, ?_, ?_⟩
  · calc ‖discriminant φ (KSPSWKB.halfNode j) -
            2 * Complex.cos (wkbPhase φ (KSPSWKB.halfNode j))‖
          ≤ CΔ / ‖KSPSWKB.halfNode j‖ ^ N := hE
        _ ≤ 2 * CΔ / ‖KSPSWKB.halfNode j‖ ^ N := by
          gcongr
          linarith
  · calc ‖KSPSWKB.primitive N φ ⟨(j, KSPSWKB.halfNode j), hchart⟩ +
            Complex.I * wkbPhase φ (KSPSWKB.halfNode j)‖
          ≤ 2 * ‖discriminant φ (KSPSWKB.halfNode j) -
              2 * Complex.cos (wkbPhase φ (KSPSWKB.halfNode j))‖ :=
            primitive_chart_error_of_phase N φ j _ hchart hθ
        _ ≤ 2 * (CΔ / ‖KSPSWKB.halfNode j‖ ^ N) := by linarith
        _ = 2 * CΔ / ‖KSPSWKB.halfNode j‖ ^ N := by ring

end
end NlsGge.ThirdConsultation.KSPS
