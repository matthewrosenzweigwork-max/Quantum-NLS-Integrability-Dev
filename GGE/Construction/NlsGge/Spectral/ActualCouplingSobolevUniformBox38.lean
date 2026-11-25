import NlsGge.Spectral.ActualHalfTraceUniformBox38Assembly

/-!
# Coupling scaling `u ↦ c • u` for the physical H¹ norm and the uniform box estimates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

theorem physicalFourier_smul38 (c : ℂ) (u : PhysicalL2) (k : ℤ) :
    physicalFourier ((c • u : PhysicalL2) : PhysicalCircle → ℂ) k = c * physicalFourier u k := by
  unfold physicalFourier fourierCoeff
  have hae : (fun t => ((c • u : PhysicalL2) : PhysicalCircle → ℂ) t) =ᵐ[spatialMeasure]
      fun t => c * (u : PhysicalCircle → ℂ) t := by
    filter_upwards [Lp.coeFn_smul c u] with t ht
    simpa using ht
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  simp only [smul_eq_mul]
  rw [ht]; ring

theorem sobolevSquareSummable_smul38 (c : ℂ) (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    SobolevSquareSummable 1 (physicalFourier ((c • u : PhysicalL2) : PhysicalCircle → ℂ)) := by
  have := hu.mul_left (‖c‖ ^ 2)
  refine this.congr (fun n => ?_)
  rw [physicalFourier_smul38, norm_mul, mul_pow]; ring

theorem physicalSobolevL2_smul_norm38 (c : ℂ) (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hu' : SobolevSquareSummable 1 (physicalFourier ((c • u : PhysicalL2) : PhysicalCircle → ℂ))) :
    ‖physicalSobolevL2 1 (c • u) hu'‖ = ‖c‖ * ‖physicalSobolevL2 1 u hu‖ := by
  have h1 := physicalSobolevL2_norm_sq 1 (c • u) hu'
  have h2 := physicalSobolevL2_norm_sq 1 u hu
  have h3 : ‖physicalSobolevL2 1 (c • u) hu'‖ ^ 2 =
      (‖c‖ * ‖physicalSobolevL2 1 u hu‖) ^ 2 := by
    rw [h1, mul_pow, h2, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    rw [physicalFourier_smul38, norm_mul, mul_pow]; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h3

theorem actualHalfTrace_uniformHalfStrip_coupling38 :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
        ‖physicalSobolevL2 1 u hu‖ ≤ R → ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) 1 →
        ∀ n : ℤ, K * R ^ 2 ≤ |(n : ℝ)| →
        ∀ z : ℂ, |z.re - n * Real.pi| ≤ 1 → 0 ≤ z.im →
          ‖Complex.exp (Complex.I * z) * actualPhysicalUnitHalfTrace32 ((τ : ℂ) • u) z -
              (1 + Complex.exp (2 * Complex.I * z)) / 2‖ ≤ C * R ^ 2 / |(n : ℝ)| := by
  obtain ⟨K, C, hK, hC, h⟩ := actualHalfTrace_uniformHalfStrip38
  refine ⟨K, C, hK, hC, ?_⟩
  intro R hR u hu huR τ hτ n hn z hz hz0
  have hu' := sobolevSquareSummable_smul38 (τ : ℂ) u hu
  refine h R hR _ hu' ?_ n hn z hz hz0
  rw [physicalSobolevL2_smul_norm38 (τ : ℂ) u hu hu', Complex.norm_real,
    Real.norm_of_nonneg hτ.1]
  calc τ * _ ≤ 1 * R := mul_le_mul hτ.2 huR (norm_nonneg _) zero_le_one
    _ = R := one_mul R

theorem actualHalfTraceBox_uniform_coupling38 :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
        ‖physicalSobolevL2 1 u hu‖ ≤ R → ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) 1 →
        ∀ n : ℤ, K * R ^ 2 ≤ |(n : ℝ)| →
          ActualHalfTraceBoxE02_38 ((τ : ℂ) • u) n (C * R ^ 2 / |(n : ℝ)|) := by
  obtain ⟨K, C, hK, hC, h⟩ := actualHalfTraceBox_uniform38
  refine ⟨K, C, hK, hC, ?_⟩
  intro R hR u hu huR τ hτ n hn
  have hu' := sobolevSquareSummable_smul38 (τ : ℂ) u hu
  refine h R hR _ hu' ?_ n hn
  rw [physicalSobolevL2_smul_norm38 (τ : ℂ) u hu hu', Complex.norm_real,
    Real.norm_of_nonneg hτ.1]
  calc τ * _ ≤ 1 * R := mul_le_mul hτ.2 huR (norm_nonneg _) zero_le_one
    _ = R := one_mul R

end NlsGge.SpectralFoundations
end

