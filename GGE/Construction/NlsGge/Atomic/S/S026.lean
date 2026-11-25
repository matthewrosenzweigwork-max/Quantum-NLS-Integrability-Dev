import Mathlib
import NlsGge.Atomic.S.S020
import NlsGge.Schur.ActualSchurF03Package38V1
import NlsGge.Schur.ActualSchurRealTypeCenter38V1
import NlsGge.Spectral.ActualGapLabelsAgreeE02_38
import NlsGge.Spectral.ActualBoxWindowUniformE02_38
import NlsGge.ThirdConsultation.S.SShared06

                                                                                                          
                                                                                   
                                                                                                             
                                                                     
                                                                                                                         
                                                                                                                    
                                                                                                                
                                                                                                      
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
open NlsGge.SpectralFoundations
namespace NlsGge.ThirdConsultation.S

theorem gapLength_ge_schurQ :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (n : ℤ),
      K * R ^ 3 ≤ |(n : ℝ)| → ∀ (w : SchurH1), ‖w‖ ≤ R →
      let ends := reflectedEndsAt n w
      let σ := (centerAt (2 * R) n (schurRealPair w)).re
      ends.1 ≤ σ ∧ σ ≤ ends.2 ∧
        2 * ‖realQAt (2 * R) n w‖ / (1 + 2 * gapParameter (2 * R) n) ≤ ends.2 - ends.1 := by
  obtain ⟨Kp, hKp, hpack⟩ := actualSchurF03Package38V1
  obtain ⟨K1, C1, hK1, hC1, hbw⟩ := actualBoxWindow_uniform_E02_38
  obtain ⟨K0, hK0, hS20⟩ := schurCenter_spec
  have hcm : (0 : ℝ) < max actualSchurCenterThresholdConstant38 1 :=
    lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨8 * Kp + K1 + K0 + 8 * max actualSchurCenterThresholdConstant38 1,
    by positivity, ?_⟩
  intro R hR n hn w hwR
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hR3 : (0 : ℝ) ≤ R ^ 3 := by positivity
  have hR2' : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR (by norm_num)
  have h2R : (1 : ℝ) ≤ 2 * R := by linarith
  have hmul : ∀ a : ℝ, 0 ≤ a → a ≤ 8 * Kp + K1 + K0 + 8 * max actualSchurCenterThresholdConstant38 1 →
      a * R ^ 3 ≤ |(n : ℝ)| :=
    fun a _ hle => le_trans (mul_le_mul_of_nonneg_right hle hR3) hn
  have hnp : Kp * (2 * R) ^ 3 ≤ |(n : ℝ)| := by
    have h := hmul (8 * Kp) (by positivity) (by linarith)
    calc Kp * (2 * R) ^ 3 = 8 * Kp * R ^ 3 := by ring
      _ ≤ |(n : ℝ)| := h
  have hthrC : actualSchurCenterThresholdConstant38 * (2 * R) ^ 3 ≤ |(n : ℝ)| := by
    have h := hmul (8 * max actualSchurCenterThresholdConstant38 1) (by positivity) (by linarith)
    have hc : actualSchurCenterThresholdConstant38 ≤ max actualSchurCenterThresholdConstant38 1 :=
      le_max_left _ _
    have h8 : (0 : ℝ) ≤ 8 * R ^ 3 := by positivity
    calc actualSchurCenterThresholdConstant38 * (2 * R) ^ 3
        = actualSchurCenterThresholdConstant38 * (8 * R ^ 3) := by ring
      _ ≤ max actualSchurCenterThresholdConstant38 1 * (8 * R ^ 3) :=
          mul_le_mul_of_nonneg_right hc h8
      _ = 8 * max actualSchurCenterThresholdConstant38 1 * R ^ 3 := by ring
      _ ≤ |(n : ℝ)| := h
  have hn0 : K0 * R ^ 3 ≤ |(n : ℝ)| := hmul K0 hK0.le (by linarith)
  have hnw : K1 * R ^ 2 ≤ |((-n : ℤ) : ℝ)| := by
    have h := hmul K1 hK1.le (by linarith)
    rw [Int.cast_neg, abs_neg]
    exact le_trans (mul_le_mul_of_nonneg_left hR2' hK1.le) h
  have hw2 : ‖w‖ ≤ 2 * R := by linarith
  have hconj : ‖actualH1Conj38 w‖ = ‖w‖ := actualH1Conj38_norm w
  have hp1 : ‖(schurRealPair w).1‖ ≤ 2 * R := hw2
  have hp2 : ‖(schurRealPair w).2‖ ≤ 2 * R := by
    change ‖actualH1Conj38 w‖ ≤ 2 * R
    rw [hconj]; exact hw2
  have hpR : ‖schurRealPair w‖ ≤ R := by
    change ‖((w, actualH1Conj38 w) : SchurPair)‖ ≤ R
    rw [Prod.norm_def]
    refine max_le hwR ?_
    rw [hconj]; exact hwR
  -- the Schur roots and their identification with the negated E02 endpoints at -n
  obtain ⟨⟨lp, lm, ⟨hlpI, hlpF⟩, ⟨hlmI, hlmF⟩⟩, hall⟩ := hpack (2 * R) h2R n hnp w hw2
  obtain ⟨⟨hlp_eq, hlm_eq⟩, ⟨hlen, hq⟩, -, -⟩ := hall lp lm hlpI hlpF hlmI hlmF
  -- E02 label agreement at -n
  have hu := physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable w
  have hnorm : ‖physicalSobolevL2 1 (physicalH1ComplexCarrierToL2Actual22 w) hu‖ ≤ R := by
    rw [physicalSobolevL2_norm_h1Carrier38]; exact hwR
  obtain ⟨hbox, hδ, hwin⟩ := hbw R hR (physicalH1ComplexCarrierToL2Actual22 w) hu hnorm (-n) hnw
  obtain ⟨hlo, hup, -⟩ := actualGapLabels_agree_E02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n)
    _ (by positivity) hδ hbox hwin
  have hE1 : (reflectedEndsAt n w).1 = lm := by
    change -actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) = lm
    rw [← hup, hlm_eq]
  have hE2 : (reflectedEndsAt n w).2 = lp := by
    change -actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) = lp
    rw [← hlo, hlp_eq]
  -- the real analytic center at radius 2R
  obtain ⟨hball, hfix, -, -, hreal⟩ := hS20 R hR n hn0 (schurRealPair w) hpR
  have him : (centerAt (2 * R) n (schurRealPair w)).im = 0 := hreal w rfl
  have hσreal : (((centerAt (2 * R) n (schurRealPair w)).re : ℝ) : ℂ) =
      centerAt (2 * R) n (schurRealPair w) := by
    apply Complex.ext <;> simp [him]
  have hσI : (centerAt (2 * R) n (schurRealPair w)).re ∈
      Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hball
    have h := le_trans (Complex.abs_re_le_norm _) hball
    rw [Complex.sub_re, abs_le] at h
    have hc : (spectralCenter n).re = Real.pi * n := by
      simp [spectralCenter, Complex.mul_re]
      ring
    rw [hc] at h
    obtain ⟨h1, h2⟩ := h
    constructor <;> linarith
  have hfix' : (((centerAt (2 * R) n (schurRealPair w)).re : ℝ) : ℂ) =
      spectralCenter n + actualSchurAlpha38 n (schurRealPair w)
        (((centerAt (2 * R) n (schurRealPair w)).re : ℝ) : ℂ) := by
    rw [hσreal]; exact hfix
  have hcmp := actualSchurGapComparison38V1 (2 * R) h2R n hthrC (schurRealPair w) hp1 hp2
    (centerAt (2 * R) n (schurRealPair w)).re lm lp hσI hlmI hlpI hfix' hlpF hlmF
  dsimp only
  rw [hE1, hE2]
  refine ⟨hcmp.1, hcmp.2.1, ?_⟩
  rw [hlen]
  exact hq

end NlsGge.ThirdConsultation.S
