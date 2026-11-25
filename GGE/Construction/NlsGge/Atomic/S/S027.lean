import Mathlib
import NlsGge.Atomic.S.S026
import NlsGge.Spectral.ActualGapActionAllNE02_38

                                                                                                          
                                                                                        
                                                                                                         
                                                                                                          
                                                                                                             
                                                                                                           
                                                                                      
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
open NlsGge.SpectralFoundations
namespace NlsGge.ThirdConsultation.S

/-- Scalar step of S-027: from `2q/(1+2d) ≤ g`, `g²/4 ≤ I`, `d ≥ 0`, `q ≥ 0` get `e^{-4d} q² ≤ I`. -/
theorem action_ge_schurQ_scalar (d q g I : ℝ) (hd : 0 ≤ d) (hq : 0 ≤ q)
    (hgap : 2 * q / (1 + 2 * d) ≤ g) (hI : g ^ 2 / 4 ≤ I) :
    Real.exp (-4 * d) * q ^ 2 ≤ I := by
  have hpos : 0 < 1 + 2 * d := by linarith
  have h2q : 2 * q ≤ g * (1 + 2 * d) := by rwa [div_le_iff₀ hpos] at hgap
  have hsq : (2 * q) ^ 2 ≤ (g * (1 + 2 * d)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2q 2
  have hI0 : 0 ≤ I := le_trans (by positivity) hI
  have hq2 : q ^ 2 ≤ I * (1 + 2 * d) ^ 2 := by
    have h4 : q ^ 2 ≤ g ^ 2 / 4 * (1 + 2 * d) ^ 2 := by nlinarith [hsq]
    exact le_trans h4 (mul_le_mul_of_nonneg_right hI (by positivity))
  have hexp1 : 1 + 2 * d ≤ Real.exp (2 * d) := by
    have := Real.add_one_le_exp (2 * d); linarith
  have hexp2 : (1 + 2 * d) ^ 2 ≤ Real.exp (4 * d) := by
    have he : Real.exp (4 * d) = Real.exp (2 * d) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [he]; exact pow_le_pow_left₀ hpos.le hexp1 2
  have hcancel : Real.exp (-4 * d) * Real.exp (4 * d) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (-4 * d) * q ^ 2 ≤ Real.exp (-4 * d) * (I * (1 + 2 * d) ^ 2) :=
        mul_le_mul_of_nonneg_left hq2 (Real.exp_pos _).le
    _ ≤ Real.exp (-4 * d) * (I * Real.exp (4 * d)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp2 hI0) (Real.exp_pos _).le
    _ = I * (Real.exp (-4 * d) * Real.exp (4 * d)) := by ring
    _ = I := by rw [hcancel, mul_one]

theorem action_ge_schurQ :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (n : ℤ),
      K * R ^ 3 ≤ |(n : ℝ)| → ∀ (w : SchurH1), ‖w‖ ≤ R →
      Real.exp (-4 * gapParameter (2 * R) n) * ‖realQAt (2 * R) n w‖ ^ 2 ≤
        reflectedActionAt n w := by
  obtain ⟨K, hK, h26⟩ := gapLength_ge_schurQ
  refine ⟨K, hK, ?_⟩
  intro R hR n hn w hw
  have h := h26 R hR n hn w hw
  dsimp only at h
  obtain ⟨-, -, hgap⟩ := h
  have hd0 : 0 ≤ gapParameter (2 * R) n := by
    unfold gapParameter actualSchurGapParameter38
    positivity
  have hlen : (reflectedEndsAt n w).2 - (reflectedEndsAt n w).1 =
      actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) -
        actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) := by
    unfold reflectedEndsAt; ring
  have hI := actualGapAction_ge_sq_div_four_all_E02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n)
  rw [← hlen] at hI
  exact action_ge_schurQ_scalar _ _ _ _ hd0 (norm_nonneg _) hgap hI

end NlsGge.ThirdConsultation.S
