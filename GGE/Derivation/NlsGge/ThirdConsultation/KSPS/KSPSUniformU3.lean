import Mathlib
import NlsGge.ThirdConsultation.KSPSInversePhaseHost
import NlsGge.ThirdConsultation.KSPS.KSPS003Host
import NlsGge.ThirdConsultation.KSPSSupport.A1U01
import NlsGge.ThirdConsultation.KSPSSupport.UNI01
import NlsGge.ThirdConsultation.KSPSSupport.EXP01

/- KSPSU3 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPSUniformU3.lean. Pro round-15 SUPPORT (never a packet).
   Item U3 of proof development's ANTITRACE_UNIFORM_STOP.md: ball-uniform bounds on the Riccati coefficients and on the
   integrated Riccati coefficients for the orders 1 <= k <= N + 1 that occur in the order-N WKB expansion
   (the antitrace/Dirichlet/endpoint formulas use only k = N + 1; h757's sketch quantified all k, which is not
   needed and is not claimed here). Route: G1_034 (orders k <= N, with membership, so psn 0 <= psn (N+1-k)),
   UNI01.h161_coef_top (order N + 1), the ball conversion ‖φ.1‖ + ‖φ.2‖ <= 2·sobolevNorm, and Cauchy–Schwarz in the
   form EXP01.h161_prefix_le at x = 1. The cover-representative form of integralRiccatiLeft is re-proved
   (same proof as proof development's KSPS025U.u1_IRL_eq, which is not landed). No hypothesis added. -/
set_option autoImplicit false
open MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.KSPSU3
noncomputable section
open NlsGge.ThirdConsultation.KSPS

theorem norm_fst_le (N : ℕ) (φ : SobolevC N) : ‖φ.1‖ ≤ sobolevNorm N φ := by
  unfold sobolevNorm
  exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))

theorem norm_snd_le (N : ℕ) (φ : SobolevC N) : ‖φ.2‖ ≤ sobolevNorm N φ := by
  unfold sobolevNorm
  exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg _))

theorem coef_L2_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 →
      ‖NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false k‖ ≤ D := by
  obtain ⟨C0, hC0, p0, hG⟩ := G1_034 N hN
  obtain ⟨D1, hD1, hTop⟩ := NlsGge.ThirdConsultation.KSPSSupport.h161_coef_top N hN (2 * B₀) (by linarith)
  refine ⟨C0 * (1 + 2 * B₀) ^ p0 + D1, add_nonneg (by positivity) hD1, fun φ hφ k hk1 hk2 => ?_⟩
  have hS : ‖φ.1‖ + ‖φ.2‖ ≤ 2 * B₀ := by linarith [norm_fst_le N φ, norm_snd_le N φ]
  rcases Nat.lt_or_ge k (N + 1) with hk | hk
  · have hA := (hG (toPotPair φ) (NlsGge.ThirdConsultation.KSPSSupport.pairSobolev_toPotPair φ)).2.2.1
      k hk1 (by omega)
    have hpair : pairSobolevNorm (N : ℝ) (toPotPair φ) ≤ 2 * B₀ :=
      (NlsGge.ThirdConsultation.KSPSSupport.h161_pair_le N φ).trans hS
    have hp0 : 0 ≤ pairSobolevNorm (N : ℝ) (toPotPair φ) :=
      NlsGge.ThirdConsultation.KSPSSupport.h161_pair_nonneg N _
    have hpow : C0 * (1 + pairSobolevNorm (N : ℝ) (toPotPair φ)) ^ p0 ≤ C0 * (1 + 2 * B₀) ^ p0 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) p0) hC0.le
    have hm := (psn_mono (m := 0) (m' := N + 1 - k) (Nat.zero_le _) hA.1).2
    rw [Nat.cast_zero, NlsGge.ThirdConsultation.KSPSSupport.h161_norm_eq_psn0] at hm
    rw [NlsGge.ThirdConsultation.KSPSSupport.h150_coef_false]
    linarith [hA.2]
  · have hkN : k = N + 1 := by omega
    subst hkN
    have h := hTop φ hS false
    rw [Nat.sub_self, Nat.cast_zero, NlsGge.ThirdConsultation.KSPSSupport.h161_norm_eq_psn0] at h
    have : 0 ≤ C0 * (1 + 2 * B₀) ^ p0 := by positivity
    linarith

theorem integralRiccatiLeft_eq_cover {N : ℕ} (φ : SobolevC N) (k : ℕ) :
    integralRiccatiLeft φ k = ∫ x in (0 : ℝ)..1,
      coverRep38 (toPotPair φ).1 x *
        coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false k) x := by
  unfold integralRiccatiLeft
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [coverRep38_ae_phys (toPotPair φ).1,
    coverRep38_ae_phys (riccatiLeft φ k)] with x h1 h2 _
  rw [h1]
  show _ = _ * coverRep38 (riccatiLeft φ k) x
  rw [h2]

theorem integralRiccatiLeft_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 →
      ‖integralRiccatiLeft φ k‖ ≤ C := by
  obtain ⟨D, hD, hDb⟩ := coef_L2_uniform N hN B₀ hB₀
  refine ⟨(B₀ ^ 2 + D ^ 2) / 2, by positivity, fun φ hφ k hk1 hk2 => ?_⟩
  rw [integralRiccatiLeft_eq_cover]
  have h := NlsGge.ThirdConsultation.KSPSSupport.h161_prefix_le (toPotPair φ).1
    (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false k) (x := 1) ⟨zero_le_one, le_rfl⟩
  have h1 : ‖(toPotPair φ).1‖ ≤ B₀ :=
    ((NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le N φ.1).trans (norm_fst_le N φ)).trans hφ
  have h2 := hDb φ hφ k hk1 hk2
  have h1s : ‖(toPotPair φ).1‖ ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2s : ‖NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false k‖ ^ 2 ≤ D ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  linarith

end
end NlsGge.ThirdConsultation.KSPSU3
