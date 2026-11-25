import NlsGge.Spectral.ComplexACPointwiseTestIntegrationByPartsV2
import NlsGge.Schur.SourceTwistedWeakDerivativeFourierCriterionV1
import NlsGge.Schur.SourceFreeDomainTwistedWeakDerivativeIffV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.Schur

/-- Absolutely continuous representatives with their actual derivative and
twisted trace satisfy the existing full source weak test predicate. The
tests retain precisely their original differentiability/L¹ hypotheses. -/
theorem sourceTwistedWeakDerivative_of_actualAC_representatives
    (n : ℤ) (F G : SourceIntervalL2) (f g : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hg : IntervalIntegrable g volume 0 1)
    (hder : ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 → HasDerivAt f (g t) t)
    (hF : F =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] f)
    (hG : G =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] g)
    (htrace : f 1 = spectralSign n * f 0) :
    SourceTwistedWeakDerivative n F G := by
  intro test testDerivative ψ ψ' ht ht' hψ hψint hψtrace
  have hboundary : f 1 * ψ 1 = f 0 * ψ 0 := by
    rw [htrace, hψtrace]
    calc
      (spectralSign n * f 0) * (spectralSign n * ψ 0) =
          (spectralSign n * spectralSign n) * (f 0 * ψ 0) := by ring
      _ = f 0 * ψ 0 := by rw [spectralSign_mul_self, one_mul]
  have hibp := NlsGge.SpectralFoundations.complex_ac_pointwise_test_integration_by_parts
    hf hg hder hψ hψint
  rw [hboundary, sub_self, zero_sub] at hibp
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hibp
  calc
    (∫ t in Set.Ioc (0 : ℝ) 1, F t * testDerivative t) =
        ∫ t in Set.Ioc (0 : ℝ) 1, f t * ψ' t := by
      apply integral_congr_ae
      filter_upwards [hF, ht'] with t hft htt
      rw [hft, htt]
    _ = -(∫ t in Set.Ioc (0 : ℝ) 1, g t * ψ t) := hibp
    _ = -(∫ t in Set.Ioc (0 : ℝ) 1, G t * test t) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hG, ht] with t hgt htt
      rw [hgt, htt]

/-- The actual weak identities above force the signed Fourier graph domain;
the source coordinate derivative is realized by AC representatives. -/
theorem sourceFreeDomain_of_actualAC_components
    (n : ℤ) (x : SectorSquare n)
    (G : Bool → SourceIntervalL2) (f g : Bool → ℝ → ℂ)
    (hf : ∀ b, AbsolutelyContinuousOnInterval (f b) 0 1)
    (hg : ∀ b, IntervalIntegrable (g b) volume 0 1)
    (hder : ∀ b, ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 →
      HasDerivAt (f b) (g b t) t)
    (hF : ∀ b, sourceCoordinateComponent n x b
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] f b)
    (hG : ∀ b, G b =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] g b)
    (htrace : ∀ b, f b 1 = spectralSign n * f b 0) :
    x ∈ freeWeightedDomainPointwise n := by
  apply (sourceFreeDomain_twisted_weak_derivative_iff n x).mpr
  refine ⟨G, ?_⟩
  intro b
  exact sourceTwistedWeakDerivative_of_actualAC_representatives n
    (sourceCoordinateComponent n x b) (G b) (f b) (g b)
    (hf b) (hg b) (hder b) (hF b) (hG b) (htrace b)

end NlsGge.Schur
end
