import Mathlib
import NlsGge.ThirdConsultation.KSPSInversePhaseHost
import NlsGge.ThirdConsultation.KSPS.KSPS003Host
import NlsGge.ThirdConsultation.KSPSSupport.A1U01
import NlsGge.ThirdConsultation.KSPSSupport.EXP01
import NlsGge.ThirdConsultation.G1.NormCalculus

/- KSPS025U1 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS025Uniform1.lean. Pro SUPPORT (never a packet).
   Head: Pro round 15 (PRO_DEFINITION_RESPONSE_FP80_15.md, Q2 "Preserve KSPS-025; add its missing quantitative
   companion"), theorem `first_two_spectral_coefficients_bounded`, VERBATIM, namespace NlsGge.ThirdConsultation.KSPS.
   grep NlsGge/ and Work/ (2026-11-02): name not defined.
   Route (Pro's): Cauchy–Schwarz (KSPSSupport.h161_prefix_le at x = 1: ‖∫₀¹ f g‖ ≤ (‖f‖² + ‖g‖²)/2), the norm-one
   H¹ → L² embedding (h161_embed_norm_le), ‖∂u‖₂ ≤ 2π‖u‖_{H¹} (psn_deriv), wkbR φ 1 = -φ₂ (G1_034, through the
   cover-representative form of integralRiccatiLeft, re-proved here verbatim from KSPS012Support11 to keep the
   closure small). Bounds obtained: ‖mass‖ ≤ B₀²/(4π), ‖momentum‖ ≤ (1+4π²)B₀²/(8π²) ≤ B₀². No hypothesis added. -/
set_option autoImplicit false

open MeasureTheory

namespace NlsGge.ThirdConsultation.KSPS025U
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.KSPS

theorem u1_norm_sq_add_le (φ : SobolevC 1) : ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 ≤ sobolevNorm 1 φ ^ 2 := by
  unfold sobolevNorm
  rw [Real.sq_sqrt (by positivity)]

theorem u1_IRL_eq (φ : SobolevC 1) (k : ℕ) :
    integralRiccatiLeft φ k = ∫ x in (0 : ℝ)..1,
      coverRep38 (toPotPair φ).1 x * coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false k) x := by
  unfold integralRiccatiLeft
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [coverRep38_ae_phys (toPotPair φ).1,
    coverRep38_ae_phys (riccatiLeft φ k)] with x h1 h2 _
  rw [h1]
  show _ = _ * coverRep38 (riccatiLeft φ k) x
  rw [h2]

theorem u1_coef1 (φ : SobolevC 1) :
    NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false 1 = -(toPotPair φ).2 := by
  obtain ⟨C0, -, p0, hG⟩ := G1_034 1 le_rfl
  exact (hG (toPotPair φ) (NlsGge.ThirdConsultation.KSPSSupport.pairSobolev_toPotPair φ)).1

theorem u1_deriv_le (φ : SobolevC 1) :
    ‖weakDerivative (toPotPair φ).2‖ ≤ 2 * Real.pi * ‖φ.2‖ := by
  obtain ⟨h1, hn⟩ := NlsGge.ThirdConsultation.KSPSSupport.h161_embed_psn1 1 le_rfl φ.2
  have hd := (psn_deriv 0 (u := physicalSobolevEmbed 1 φ.2) (by simpa using h1)).2
  have e := NlsGge.ThirdConsultation.KSPSSupport.h161_norm_eq_psn0
    (weakDerivative (physicalSobolevEmbed 1 φ.2))
  simp only [Nat.cast_zero, zero_add, Nat.cast_one] at hd
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  show ‖weakDerivative (physicalSobolevEmbed 1 φ.2)‖ ≤ _
  rw [← e]
  exact hd.trans (mul_le_mul_of_nonneg_left hn hpi)

end
end NlsGge.ThirdConsultation.KSPS025U

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem first_two_spectral_coefficients_bounded
    (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B₀ →
      ‖massCoefficient φ‖ ≤ B₀^2 ∧
      ‖momentumCoefficient φ‖ ≤ B₀^2 := by
  intro φ hφ
  have hpi := Real.pi_gt_three
  have hs0 : 0 ≤ sobolevNorm 1 φ := Real.sqrt_nonneg _
  have hsq : sobolevNorm 1 φ ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ hs0 hφ 2
  have hsum := NlsGge.ThirdConsultation.KSPS025U.u1_norm_sq_add_le φ
  have he1 : ‖(toPotPair φ).1‖ ≤ ‖φ.1‖ := NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le 1 φ.1
  have he2 : ‖(toPotPair φ).2‖ ≤ ‖φ.2‖ := NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le 1 φ.2
  have a1 : ‖(toPotPair φ).1‖ ^ 2 ≤ ‖φ.1‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) he1 2
  have a2 : ‖(toPotPair φ).2‖ ^ 2 ≤ ‖φ.2‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) he2 2
  have hd := NlsGge.ThirdConsultation.KSPS025U.u1_deriv_le φ
  have a3 : ‖NlsGge.GKDefinitionDesign.weakDerivative (toPotPair φ).2‖ ^ 2 ≤ (2 * Real.pi) ^ 2 * ‖φ.2‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hd 2
    rw [mul_pow] at this
    exact this
  have hB2 : 0 ≤ B₀ ^ 2 := sq_nonneg _
  constructor
  · -- mass
    have h := NlsGge.ThirdConsultation.KSPS025U.u1_IRL_eq φ 1
    rw [NlsGge.ThirdConsultation.KSPS025U.u1_coef1] at h
    have hI : ‖integralRiccatiLeft φ 1‖ ≤ (‖(toPotPair φ).1‖ ^ 2 + ‖-(toPotPair φ).2‖ ^ 2) / 2 := by
      rw [h]
      exact NlsGge.ThirdConsultation.KSPSSupport.h161_prefix_le _ _ ⟨zero_le_one, le_rfl⟩
    rw [norm_neg] at hI
    have hI' : ‖integralRiccatiLeft φ 1‖ ≤ B₀ ^ 2 := by linarith
    unfold massCoefficient
    rw [norm_mul, norm_neg, norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    have hinv : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    calc (2 * Real.pi)⁻¹ * ‖integralRiccatiLeft φ 1‖ ≤ 1 * B₀ ^ 2 :=
          mul_le_mul hinv hI' (norm_nonneg _) zero_le_one
      _ = B₀ ^ 2 := one_mul _
  · -- momentum
    have hI : ‖NlsGge.ThirdConsultation.KSPSRiccati.momentumIntegral φ‖ ≤
        (‖(toPotPair φ).1‖ ^ 2 + ‖NlsGge.GKDefinitionDesign.weakDerivative (toPotPair φ).2‖ ^ 2) / 2 :=
      NlsGge.ThirdConsultation.KSPSSupport.h161_prefix_le _ _ ⟨zero_le_one, le_rfl⟩
    have hφ1 : ‖φ.1‖ ^ 2 ≤ B₀ ^ 2 := by nlinarith [sq_nonneg ‖φ.2‖]
    have hφ2 : ‖φ.2‖ ^ 2 ≤ B₀ ^ 2 := by nlinarith [sq_nonneg ‖φ.1‖]
    have hpi2 : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
    have hc : (2 * Real.pi) ^ 2 * ‖φ.2‖ ^ 2 ≤ (2 * Real.pi) ^ 2 * B₀ ^ 2 :=
      mul_le_mul_of_nonneg_left hφ2 hpi2
    have hI' : ‖NlsGge.ThirdConsultation.KSPSRiccati.momentumIntegral φ‖ ≤
        (B₀ ^ 2 + (2 * Real.pi) ^ 2 * B₀ ^ 2) / 2 := by linarith
    unfold momentumCoefficient
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, norm_inv, norm_mul, Complex.norm_ofNat,
      norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hp : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
    rw [inv_mul_le_iff₀ hp]
    have : (B₀ ^ 2 + (2 * Real.pi) ^ 2 * B₀ ^ 2) / 2 ≤ 4 * Real.pi ^ 2 * B₀ ^ 2 := by
      have e : (B₀ ^ 2 + (2 * Real.pi) ^ 2 * B₀ ^ 2) / 2 = B₀ ^ 2 / 2 + 2 * Real.pi ^ 2 * B₀ ^ 2 := by ring
      rw [e]
      have h9 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h9 hB2]
    linarith

end
end NlsGge.ThirdConsultation.KSPS
