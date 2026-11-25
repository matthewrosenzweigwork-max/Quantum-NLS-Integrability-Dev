import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS003Host
import NlsGge.ThirdConsultation.KSPS.KSPS015Host
import NlsGge.ThirdConsultation.KSPS.KSPS025Host
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform2

/- KSPS025U3 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS025Uniform3.lean. Pro SUPPORT (never a packet); CONDITIONAL.
   `midpoint_first_order_uniform_of`: Pro round 15's `midpoint_first_order_uniform` conclusion (Q2, verbatim body)
   from two explicit hypotheses of EXACTLY Pro's printed head types:
     hexp = `KSPS.midpoint_spectral_expansion_uniform` (not yet proved), hcoef = `KSPS.first_two_spectral_coefficients_bounded`
     (proof development KSPS025U1, pending review).
   Route = Pro's: F = {k} in the finite-sum bound gives ‖midpoint - spectralPolynomial‖ ≤ C/|k|² (indexWeight k ^ 2 =
   1 + k² ≥ |k|²); the exact N = 1 polynomial (KSPS025U2.spectralPolynomial_one_eq) and ‖momentum‖ ≤ B₀² give the
   numerator C + B₀²; B = 1 + C + B₀². When both hypotheses are theorems, the Pro head follows by application. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS025U3
noncomputable section
open NlsGge.Pilot
open NlsGge.ThirdConsultation.KSPS

theorem indexWeight_sq_eq (k : ℤ) : indexWeight k ^ (1 + 1) = 1 + (k : ℝ) ^ 2 := by
  unfold indexWeight
  rw [show (1 + 1 : ℕ) = 2 from rfl, Real.sq_sqrt (by positivity)]

theorem natAbs_sq_le_indexWeight_sq (k : ℤ) : (k.natAbs : ℝ) ^ 2 ≤ indexWeight k ^ (1 + 1) := by
  rw [indexWeight_sq_eq, Nat.cast_natAbs, Int.cast_abs, sq_abs]
  linarith

theorem midpoint_first_order_uniform_of
    (hexp : ∀ (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
          WeightedL2Error ((N + 1 : ℕ) : ℝ)
            (fun n => midpoint φ n - spectralPolynomial φ n) ∧
          ∀ F : Finset ℤ,
            (∑ n ∈ F,
              (indexWeight n ^ (N + 1) *
                ‖midpoint φ n - spectralPolynomial φ n‖)^2) ≤ C^2)
    (hcoef : ∀ (B₀ : ℝ) (hB₀ : 0 ≤ B₀),
      ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B₀ →
        ‖massCoefficient φ‖ ≤ B₀^2 ∧
        ‖momentumCoefficient φ‖ ≤ B₀^2)
    (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ B : ℝ, 0 < B ∧
      ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B₀ →
        ‖massCoefficient φ‖ ≤ B ∧
        ∀ k : ℤ, k ≠ 0 →
          ‖midpoint φ k - (k : ℂ) * Real.pi -
            massCoefficient φ / (k : ℂ)‖ ≤
              B / (k.natAbs : ℝ)^2 := by
  obtain ⟨C, hC, hE⟩ := hexp 1 le_rfl B₀ hB₀
  refine ⟨1 + C + B₀ ^ 2, by positivity, fun φ hφ => ?_⟩
  obtain ⟨hm, hp⟩ := hcoef B₀ hB₀ φ hφ
  refine ⟨by nlinarith, fun k hk => ?_⟩
  have hF := (hE φ hφ).2 {k}
  rw [Finset.sum_singleton] at hF
  have hk0 : (0 : ℝ) < (k.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.2 hk
  have hk2 : (0 : ℝ) < (k.natAbs : ℝ) ^ 2 := by positivity
  have hw0 : 0 ≤ indexWeight k ^ (1 + 1) := by unfold indexWeight; positivity
  have h1 : indexWeight k ^ (1 + 1) * ‖midpoint φ k - spectralPolynomial φ k‖ ≤ C :=
    (sq_le_sq₀ (mul_nonneg hw0 (norm_nonneg _)) hC).1 hF
  have h2 : (k.natAbs : ℝ) ^ 2 * ‖midpoint φ k - spectralPolynomial φ k‖ ≤ C :=
    le_trans (mul_le_mul_of_nonneg_right (natAbs_sq_le_indexWeight_sq k) (norm_nonneg _)) h1
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hnk : ‖(k : ℂ) ^ 2‖ = (k.natAbs : ℝ) ^ 2 := by
    rw [norm_pow, Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
  have h3 : (k.natAbs : ℝ) ^ 2 * ‖momentumCoefficient φ / (k : ℂ) ^ 2‖ ≤ B₀ ^ 2 := by
    rw [norm_div, hnk, mul_div_cancel₀ _ hk2.ne']
    exact hp
  have e : midpoint φ k - (k : ℂ) * Real.pi - massCoefficient φ / (k : ℂ) =
      (midpoint φ k - spectralPolynomial φ k) - momentumCoefficient φ / (k : ℂ) ^ 2 := by
    rw [NlsGge.ThirdConsultation.KSPS025U2.spectralPolynomial_one_eq]
    ring
  rw [e, le_div_iff₀ hk2]
  have h4 := norm_sub_le (midpoint φ k - spectralPolynomial φ k) (momentumCoefficient φ / (k : ℂ) ^ 2)
  nlinarith

end
end NlsGge.ThirdConsultation.KSPS025U3
