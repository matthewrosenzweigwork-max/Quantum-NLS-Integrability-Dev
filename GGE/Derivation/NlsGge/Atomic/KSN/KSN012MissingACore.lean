import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS025Host
import NlsGge.ThirdConsultation.KSPS.KSPS023Host
import NlsGge.ThirdConsultation.KSPS.KSPS019Host
import NlsGge.ThirdConsultation.KSPS.KSPS015Host
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU4
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform0
import NlsGge.Atomic.KSN.KSN012Sup7Core

/- KSN012MACore PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). CORE.
   Target NlsGge/Atomic/KSN/KSN012MissingACore.lean. SUPPORT (no packet increment) for KSN-012.
   missingA_of: the body of proof development's KSN012_missingA (KSN012_MISSINGPROBE01, verbatim) from three hypotheses whose
   types are EXACTLY Pro round-15 `KSPS.midpoint_spectral_expansion_uniform`, `KSPS.midpoint_dirichlet_difference_uniform`
   (proved in KSPS017Uniform7) and the h24 binder (= KSPS017U6.h24_uniform), all used at N = 1 only.
   Route (the decomposition named in proof development/KSN012_STOP.md, "KSPS-023 minus KSPS-024"):
     μ − λ̇ = −(midpoint − μ + F/2) + F/2 + (midpoint − P) − (λ̇ − P),   F = φ̂₁(−n) + φ̂₂(n), P = spectralPolynomial,
   so w|μ − λ̇| ≤ w²|D| + w|φ̂₁(−n)| + w|φ̂₂(n)| + w²|midpoint − P| + w²|λ̇ − P| (w ≥ 1); the three w²-terms have uniform
   finite tail sums by the hypotheses and the Fourier terms by KSPSU4.weighted_fourier_le (≤ B²). Finite partial sums
   give the ENNReal tsum bound (KSN012U.sup7_tsum_ofReal_le). No hypothesis added to the target. -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSN012MA
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS

theorem w_one_le (n : ℤ) : 1 ≤ indexWeight n := by
  unfold indexWeight
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (n : ℝ)])

theorem pointwise (φ : SobolevC 1) (n : ℤ) :
    indexWeight n * ‖mu φ n - criticalEigenvalue φ n‖ ≤
      indexWeight n ^ (1 + 1) * ‖midpoint φ n - mu φ n +
          (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2‖ +
        indexWeight n ^ 1 * ‖physicalFourier (toPotPair φ).1 (-n)‖ +
        indexWeight n ^ 1 * ‖physicalFourier (toPotPair φ).2 n‖ +
        indexWeight n ^ (1 + 1) * ‖midpoint φ n - spectralPolynomial φ n‖ +
        indexWeight n ^ (1 + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖ := by
  set w : ℝ := indexWeight n with hw
  have hw1 : 1 ≤ w := w_one_le n
  set D : ℂ := midpoint φ n - mu φ n +
    (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2 with hD
  set a : ℂ := physicalFourier (toPotPair φ).1 (-n) with ha
  set b : ℂ := physicalFourier (toPotPair φ).2 n with hb
  set E : ℂ := midpoint φ n - spectralPolynomial φ n with hE
  set G : ℂ := criticalEigenvalue φ n - spectralPolynomial φ n with hG
  have e : mu φ n - criticalEigenvalue φ n = -D + a / 2 + b / 2 + E - G := by
    rw [hD, hE, hG, ha, hb]; ring
  have hn : ‖mu φ n - criticalEigenvalue φ n‖ ≤ ‖D‖ + ‖a‖ + ‖b‖ + ‖E‖ + ‖G‖ := by
    rw [e]
    have h1 := norm_sub_le (-D + a / 2 + b / 2 + E) G
    have h2 := norm_add_le (-D + a / 2 + b / 2) E
    have h3 := norm_add_le (-D + a / 2) (b / 2)
    have h4 := norm_add_le (-D) (a / 2)
    rw [norm_neg] at h4
    have h5 : ‖a / 2‖ ≤ ‖a‖ := by rw [norm_div, Complex.norm_ofNat]; linarith [norm_nonneg a]
    have h6 : ‖b / 2‖ ≤ ‖b‖ := by rw [norm_div, Complex.norm_ofNat]; linarith [norm_nonneg b]
    linarith
  have hw0 : 0 ≤ w := by linarith
  have hww : w ≤ w ^ (1 + 1) := by
    rw [show (1 + 1 : ℕ) = 2 from rfl, sq]; nlinarith
  have k1 : w * ‖D‖ ≤ w ^ (1 + 1) * ‖D‖ := mul_le_mul_of_nonneg_right hww (norm_nonneg _)
  have k2 : w * ‖E‖ ≤ w ^ (1 + 1) * ‖E‖ := mul_le_mul_of_nonneg_right hww (norm_nonneg _)
  have k3 : w * ‖G‖ ≤ w ^ (1 + 1) * ‖G‖ := mul_le_mul_of_nonneg_right hww (norm_nonneg _)
  have k0 := mul_le_mul_of_nonneg_left hn hw0
  rw [pow_one]
  nlinarith [k0, k1, k2, k3]

theorem missingA_of
    (hexp : ∀ (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
          WeightedL2Error ((N + 1 : ℕ) : ℝ)
            (fun n => midpoint φ n - spectralPolynomial φ n) ∧
          ∀ F : Finset ℤ,
            (∑ n ∈ F,
              (indexWeight n ^ (N + 1) *
                ‖midpoint φ n - spectralPolynomial φ n‖)^2) ≤ C^2)
    (hdir : ∀ (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
          WeightedL2Error ((N + 1 : ℕ) : ℝ)
            (fun n => midpoint φ n - mu φ n +
              (physicalFourier (toPotPair φ).1 (-n) +
               physicalFourier (toPotPair φ).2 n) / 2) ∧
          ∀ F : Finset ℤ,
            (∑ n ∈ F,
              (indexWeight n ^ (N + 1) *
                ‖midpoint φ n - mu φ n +
                  (physicalFourier (toPotPair φ).1 (-n) +
                   physicalFourier (toPotPair φ).2 n) / 2‖)^2) ≤ C^2)
    (h24 : ∀ (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀),
      ∃ (M : ℕ) (C : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        ∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) →
          ∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖) ^ 2 ≤ C) :
    ∀ B : ℝ, 0 < B → ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC 1, NlsGge.ThirdConsultation.KSPS.sobolevNorm 1 φ ≤ B →
        (∑' n : ℤ, if N ≤ n.natAbs then
          ENNReal.ofReal (NlsGge.ThirdConsultation.KSPS.indexWeight n ^ 2 *
            ‖NlsGge.ThirdConsultation.KSPS.mu φ n - NlsGge.ThirdConsultation.KSPS.criticalEigenvalue φ n‖ ^ 2)
          else 0) ≤ ENNReal.ofReal C := by
  intro B hB
  obtain ⟨C1, hC1, hE⟩ := hexp 1 le_rfl B hB.le
  obtain ⟨C2, hC2, hDd⟩ := hdir 1 le_rfl B hB.le
  obtain ⟨M, C3, hG⟩ := h24 1 le_rfl B hB.le
  set Ct : ℝ := 1 ^ 2 * (((5 : ℕ) : ℝ) * (C2 ^ 2 + B ^ 2 + B ^ 2 + C1 ^ 2 + max C3 0)) with hCt
  refine ⟨Ct, M, by positivity, fun φ hφ => ?_⟩
  have hfun : (fun n : ℤ => if M ≤ n.natAbs then
      ENNReal.ofReal (indexWeight n ^ 2 * ‖mu φ n - criticalEigenvalue φ n‖ ^ 2) else 0) =
      fun n : ℤ => ENNReal.ofReal (if M ≤ n.natAbs then
        indexWeight n ^ 2 * ‖mu φ n - criticalEigenvalue φ n‖ ^ 2 else 0) := by
    funext n; split_ifs <;> simp
  rw [hfun]
  refine NlsGge.ThirdConsultation.KSN012U.sup7_tsum_ofReal_le _ (fun n => by split_ifs <;> positivity) Ct
    (fun F => ?_)
  set F' : Finset ℤ := F.filter (fun n => M ≤ n.natAbs) with hF'
  have hF'M : ∀ n ∈ F', (M : ℤ) ≤ |n| := by
    intro n hn
    have h := (Finset.mem_filter.1 hn).2
    have : ((n.natAbs : ℕ) : ℤ) = |n| := Int.natCast_natAbs n
    omega
  have hsplit : ∑ n ∈ F, (if M ≤ n.natAbs then
      indexWeight n ^ 2 * ‖mu φ n - criticalEigenvalue φ n‖ ^ 2 else 0) =
      ∑ n ∈ F', (indexWeight n * ‖mu φ n - criticalEigenvalue φ n‖) ^ 2 := by
    rw [hF', Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    split_ifs <;> ring
  rw [hsplit]
  have hW := NlsGge.ThirdConsultation.KSPSU4.weighted_fourier_le 1 φ F'
  have hs0 : 0 ≤ sobolevNorm 1 φ := by unfold sobolevNorm; exact Real.sqrt_nonneg _
  have hB2 : sobolevNorm 1 φ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hs0 hφ 2
  have hFa0 : 0 ≤ ∑ n ∈ F', (indexWeight n ^ 1 * ‖physicalFourier (toPotPair φ).1 (-n)‖) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hFb0 : 0 ≤ ∑ n ∈ F', (indexWeight n ^ 1 * ‖physicalFourier (toPotPair φ).2 n‖) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine NlsGge.ThirdConsultation.KSPS017U0.sum_sq_le_fin F' _
    ![fun n => indexWeight n ^ (1 + 1) * ‖midpoint φ n - mu φ n +
          (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2‖,
      fun n => indexWeight n ^ 1 * ‖physicalFourier (toPotPair φ).1 (-n)‖,
      fun n => indexWeight n ^ 1 * ‖physicalFourier (toPotPair φ).2 n‖,
      fun n => indexWeight n ^ (1 + 1) * ‖midpoint φ n - spectralPolynomial φ n‖,
      fun n => indexWeight n ^ (1 + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖]
    1 zero_le_one ?_ ![C2 ^ 2, B ^ 2, B ^ 2, C1 ^ 2, max C3 0] ?_ |>.trans (le_of_eq ?_)
  · intro n _
    refine ⟨mul_nonneg (le_trans zero_le_one (w_one_le n)) (norm_nonneg _), ?_⟩
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero,
      one_mul]
    have h := pointwise φ n
    linarith
  · intro j
    fin_cases j
    · exact (hDd φ hφ).2 F'
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      linarith
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      linarith
    · exact (hE φ hφ).2 F'
    · exact (hG φ hφ F' hF'M).trans (le_max_left _ _)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
    rw [hCt]; ring

end
end NlsGge.ThirdConsultation.KSN012MA
