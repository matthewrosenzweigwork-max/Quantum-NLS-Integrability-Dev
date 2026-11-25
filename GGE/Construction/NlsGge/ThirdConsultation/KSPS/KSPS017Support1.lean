import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS017Host
import NlsGge.ThirdConsultation.KSPS.KSPS014Host

                                                                                                                    
                                                                                                                   
                                                                                                           
                                                                                                
                                                                                                           
                                                                                                         
                                                                                            
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem phaseDerivative_eq_deriv
    (N : ℕ) (φ : SobolevC N) (lam : ℂ) (hlam : lam ≠ 0) :
    HasDerivAt (wkbPhase φ) (KSPSWKB.phaseDerivative φ lam) lam := by
  have hf : wkbPhase φ = fun z : ℂ => z + Complex.I * ∑ k ∈ Finset.Icc 1 N,
      ((2 * Complex.I) ^ (-(k : ℤ)) * integralRiccatiLeft φ k) * z ^ (-(k : ℤ)) := by
    funext z
    unfold wkbPhase
    congr 2
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mul_zpow]; ring
  have hs : HasDerivAt (fun z : ℂ => ∑ k ∈ Finset.Icc 1 N,
      ((2 * Complex.I) ^ (-(k : ℤ)) * integralRiccatiLeft φ k) * z ^ (-(k : ℤ)))
      (∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I) ^ (-(k : ℤ)) * integralRiccatiLeft φ k) *
        (((-(k : ℤ) : ℤ) : ℂ) * lam ^ (-(k : ℤ) - 1))) lam :=
    HasDerivAt.fun_sum (fun k _ => (hasDerivAt_zpow (-(k : ℤ)) lam (Or.inl hlam)).const_mul _)
  rw [hf]
  refine ((hasDerivAt_id' lam).add (hs.const_mul Complex.I)).congr_deriv ?_
  unfold KSPSWKB.phaseDerivative
  rw [sub_eq_add_neg, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 2
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have e : (-(k : ℤ) - 1) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e]
  push_cast
  ring

end
end NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS017W
noncomputable section
open NlsGge.ThirdConsultation.KSPS

theorem hasDerivAt_eps (N : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun w : ℂ => ((2 * Complex.I * w) ^ N)⁻¹)
      (-((N : ℂ) * z⁻¹ * ((2 * Complex.I * z) ^ N)⁻¹)) z := by
  have hf : (fun w : ℂ => ((2 * Complex.I * w) ^ N)⁻¹) =
      fun w : ℂ => (2 * Complex.I) ^ (-(N : ℤ)) * w ^ (-(N : ℤ)) := by
    funext w
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_pow, mul_inv]
  rw [hf]
  convert (hasDerivAt_zpow (-(N : ℤ)) z (Or.inl hz)).const_mul ((2 * Complex.I) ^ (-(N : ℤ))) using 1
  rw [zpow_sub_one₀ hz, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_pow, mul_inv]
  push_cast
  ring

theorem hasDerivAt_invPowSum (N : ℕ) (c : ℕ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun w : ℂ => ∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * w) ^ k)⁻¹ * c k)
      (∑ k ∈ Finset.Icc 1 N, -((k : ℂ) * z⁻¹ * ((2 * Complex.I * z) ^ k)⁻¹) * c k) z :=
  HasDerivAt.fun_sum (fun k _ => (hasDerivAt_eps k hz).mul_const (c k))

theorem norm_inv_two_I_pow_le {z : ℂ} (hz : 1 ≤ ‖z‖) {k : ℕ} (hk : 1 ≤ k) :
    ‖((2 * Complex.I * z) ^ k)⁻¹‖ ≤ ‖z‖⁻¹ := by
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz
  rw [norm_inv, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  have h1 : 1 ≤ 2 * ‖z‖ := by linarith
  have h2 : (2 * ‖z‖) ^ 1 ≤ (2 * ‖z‖) ^ k := pow_le_pow_right₀ h1 hk
  rw [pow_one] at h2
  exact inv_anti₀ hz0 (by linarith)

theorem norm_invPowSum_deriv_le (N : ℕ) (c : ℕ → ℂ) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖∑ k ∈ Finset.Icc 1 N, -((k : ℂ) * z⁻¹ * ((2 * Complex.I * z) ^ k)⁻¹) * c k‖ ≤
      (∑ k ∈ Finset.Icc 1 N, (k : ℝ) * ‖c k‖) / ‖z‖ ^ 2 := by
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => ?_))
  have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
  rw [norm_mul, norm_neg, norm_mul, norm_mul, Complex.norm_natCast, norm_inv]
  have hb := norm_inv_two_I_pow_le hz hk1
  have hc : 0 ≤ ‖c k‖ := norm_nonneg _
  have hkk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc (k : ℝ) * ‖z‖⁻¹ * ‖((2 * Complex.I * z) ^ k)⁻¹‖ * ‖c k‖
      ≤ (k : ℝ) * ‖z‖⁻¹ * ‖z‖⁻¹ * ‖c k‖ := by
        gcongr
    _ = (k : ℝ) * ‖c k‖ / ‖z‖ ^ 2 := by field_simp

/-- alpha(., 0) and beta(., 0): derivative exists at every nonzero point and is bounded by K/|z|^2 on |z| >= 1. -/
theorem endpointCoeff_deriv {N : ℕ} (φ : SobolevC N) (b : Bool) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, 1 ≤ ‖z‖ →
      ∃ d : ℂ, HasDerivAt (fun w : ℂ => -Complex.I * ∑ k ∈ Finset.Icc 1 N,
          ((2 * Complex.I * w) ^ k)⁻¹ * KSPSWKB.coefficientTrace φ b k 0) d z ∧ ‖d‖ ≤ K / ‖z‖ ^ 2 := by
  refine ⟨∑ k ∈ Finset.Icc 1 N, (k : ℝ) * ‖KSPSWKB.coefficientTrace φ b k 0‖,
    Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg k) (norm_nonneg _)), fun z hz => ?_⟩
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; norm_num at hz
  refine ⟨_, (hasDerivAt_invPowSum N (fun k => KSPSWKB.coefficientTrace φ b k 0) hz0).const_mul (-Complex.I), ?_⟩
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact norm_invPowSum_deriv_le N _ hz

theorem alpha_fun_eq {N : ℕ} (φ : SobolevC N) :
    (fun w : ℂ => KSPSWKB.alpha φ w 0) = (fun w : ℂ => -Complex.I * ∑ k ∈ Finset.Icc 1 N,
          ((2 * Complex.I * w) ^ k)⁻¹ * KSPSWKB.coefficientTrace φ false k 0) := rfl

theorem beta_fun_eq {N : ℕ} (φ : SobolevC N) :
    (fun w : ℂ => KSPSWKB.beta φ w 0) = (fun w : ℂ => -Complex.I * ∑ k ∈ Finset.Icc 1 N,
          ((2 * Complex.I * w) ^ k)⁻¹ * KSPSWKB.coefficientTrace φ true k 0) := rfl

end
end NlsGge.ThirdConsultation.KSPS017W
