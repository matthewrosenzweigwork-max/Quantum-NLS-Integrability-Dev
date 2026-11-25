import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS003Host
import NlsGge.ThirdConsultation.KSPSSupport.A1U01

/- KSPSU4 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPSUniformU4.lean. Pro round-15 SUPPORT (never a packet).
   Item U4 of proof development's ANTITRACE_UNIFORM_STOP.md (elementary norm bounds, constants depending only on the
   Sobolev norm):
     weighted_fourier_le : ∀ F, Σ_F (w^N ‖φ̂₁(-n)‖)² + Σ_F (w^N ‖φ̂₂(n)‖)² ≤ sobolevNorm N φ²
     l2_norm_sq_le       : ‖(toPotPair φ).1‖² + ‖(toPotPair φ).2‖² ≤ sobolevNorm N φ²
     potL1Norm38_le      : potL1Norm38 (toPotPair φ) ≤ 1 + sobolevNorm N φ² / 2
   (the last is AM-GM pointwise, ‖r‖ ≤ (‖r‖² + 1)/2, plus ∫₀¹‖coverRep38 f‖² = ‖f‖²; h757's suggested constant
   2·sobolevNorm was marked unchecked and is not used). Route: Parseval for the Sobolev carrier
   (Birkhoff.carrier_hasSum_norm_sq38), physicalFourier(embed u) n = -carrierCoe(u)(-n), mode weight = w^(2N).
   No hypothesis added. -/
set_option autoImplicit false
open MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GK38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSPSU4
noncomputable section
open NlsGge.ThirdConsultation.KSPS

theorem pf_embed_eq (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) (n : ℤ) :
    physicalFourier (physicalSobolevEmbed m u) n =
      -carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) u) (-n) := by
  have h1 := fourierSeq38_apply (physicalSobolevEmbed m u) (-n)
  rw [neg_neg, physicalSobolevEmbed_fourier] at h1
  rw [h1]; ring

theorem modeWeight_eq (N : ℕ) (n : ℤ) :
    sobolevModeWeight (N : ℝ) n = (indexWeight n ^ N) ^ 2 := by
  rw [NlsGge.NLS38.sobolevModeWeight_natCast_eq, ← pow_mul, mul_comm 2 N]
  rfl

theorem component_le (N : ℕ) (u : PhysicalSobolev38 (N : ℝ)) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (F : Finset ℤ) :
    ∑ n ∈ F, (indexWeight n ^ N * ‖physicalFourier (physicalSobolevEmbed N u) (s * n)‖) ^ 2 ≤
      ‖u‖ ^ 2 := by
  set c := carrierCoe38 (N : ℝ) (physicalSobolevFourierEquiv38 (N : ℝ) u)
  have H := carrier_hasSum_norm_sq38 (N : ℝ) (physicalSobolevFourierEquiv38 (N : ℝ) u)
  rw [LinearIsometryEquiv.norm_map] at H
  have hle : ∀ G : Finset ℤ, ∑ n ∈ G, sobolevModeWeight (N : ℝ) n * ‖c n‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    intro G
    rw [← H.tsum_eq]
    exact H.summable.sum_le_tsum G (fun n _ => mul_nonneg ((sobolevModeWeightPositive (N : ℝ)).out n).le (sq_nonneg _))
  have hterm : ∀ n : ℤ, (indexWeight n ^ N * ‖physicalFourier (physicalSobolevEmbed N u) (s * n)‖) ^ 2 =
      sobolevModeWeight (N : ℝ) (-(s * n)) * ‖c (-(s * n))‖ ^ 2 := by
    intro n
    rw [pf_embed_eq, norm_neg, sobolevModeWeight_neg, modeWeight_eq, mul_pow]
    have hw : indexWeight (-n) = indexWeight n := by simp [indexWeight]
    rcases hs with rfl | rfl
    · simp only [one_mul]
      try rw [hw]
      try rfl
    · simp only [neg_mul, one_mul, neg_neg]
      try rw [hw]
      try rfl
  simp_rw [hterm]
  have hinj : Set.InjOn (fun n : ℤ => -(s * n)) F := by
    intro x _ y _ h
    rcases hs with rfl | rfl <;> simp at h <;> exact h
  rw [← Finset.sum_image (f := fun m => sobolevModeWeight (N : ℝ) m * ‖c m‖ ^ 2) hinj]
  exact hle _

theorem weighted_fourier_le (N : ℕ) (φ : SobolevC N) (F : Finset ℤ) :
    (∑ n ∈ F, (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖) ^ 2) +
    (∑ n ∈ F, (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖) ^ 2) ≤
      sobolevNorm N φ ^ 2 := by
  have h1 := component_le N φ.1 (-1) (Or.inr rfl) F
  have h2 := component_le N φ.2 1 (Or.inl rfl) F
  simp only [neg_mul, one_mul] at h1 h2
  have e : sobolevNorm N φ ^ 2 = ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
    unfold sobolevNorm; exact Real.sq_sqrt (by positivity)
  rw [e]
  exact add_le_add h1 h2

theorem l2_norm_sq_le (N : ℕ) (φ : SobolevC N) :
    ‖(toPotPair φ).1‖ ^ 2 + ‖(toPotPair φ).2‖ ^ 2 ≤ sobolevNorm N φ ^ 2 := by
  have e : sobolevNorm N φ ^ 2 = ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2 := by
    unfold sobolevNorm; exact Real.sq_sqrt (by positivity)
  rw [e]
  have h1 := NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le N φ.1
  have h2 := NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le N φ.2
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h1 2) (pow_le_pow_left₀ (norm_nonneg _) h2 2)

theorem integral_norm_coverRep_le (f : PhysicalL2) :
    ∫ t in (0 : ℝ)..1, ‖coverRep38 f t‖ ≤ (‖f‖ ^ 2 + 1) / 2 := by
  have hi2 := intervalIntegrable_coverRep38_sq_one f
  have hg : IntervalIntegrable (fun t => (‖coverRep38 f t‖ ^ 2 + 1) / 2) volume 0 1 :=
    (hi2.add intervalIntegrable_const).div_const 2
  have h1 : ∫ t in (0 : ℝ)..1, ‖coverRep38 f t‖ ≤
      ∫ t in (0 : ℝ)..1, (‖coverRep38 f t‖ ^ 2 + 1) / 2 :=
    intervalIntegral.integral_mono_on zero_le_one (intervalIntegrable_norm_coverRep38_one f) hg
      (fun t _ => by nlinarith [sq_nonneg (‖coverRep38 f t‖ - 1)])
  have h2 : ∫ t in (0 : ℝ)..1, (‖coverRep38 f t‖ ^ 2 + 1) / 2 = (‖f‖ ^ 2 + 1) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi2 intervalIntegrable_const,
      integral_sq_coverRep38_one]
    simp
  linarith

theorem potL1Norm38_le (N : ℕ) (φ : SobolevC N) :
    potL1Norm38 (toPotPair φ) ≤ 1 + sobolevNorm N φ ^ 2 / 2 := by
  unfold potL1Norm38 potRepFst38 potRepSnd38
  rw [intervalIntegral.integral_add (intervalIntegrable_norm_coverRep38_one _)
    (intervalIntegrable_norm_coverRep38_one _)]
  have h1 := integral_norm_coverRep_le (toPotPair φ).1
  have h2 := integral_norm_coverRep_le (toPotPair φ).2
  have h3 := l2_norm_sq_le N φ
  linarith

end
end NlsGge.ThirdConsultation.KSPSU4
