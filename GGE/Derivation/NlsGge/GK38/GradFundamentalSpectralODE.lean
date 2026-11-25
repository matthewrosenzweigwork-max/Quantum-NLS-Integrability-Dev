import NlsGge.GK38.GradFundamentalSpectralRemainder

/-! # K1: AC and the actual forced spectral variational ODE.
GK Chapter I, Proposition3.1. The independently constructed diagonal resolvent
has zero initial value and forcing ZM on the closed unit interval.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory Set
namespace NlsGge.GK38
noncomputable section

def spectralVariationGauge38 (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 :=
  Matrix.of fun i j => spectralGaugeSource38 z (fundContP φ z) s i j +
    (freeE z (-s) * potCoeff38 φ s * ext38 (fundSpectralResolvent38 φ z) s) i j

theorem intervalIntegrable_spectralVariationGauge38 (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    IntervalIntegrable (fun s => spectralVariationGauge38 φ z s i j) volume 0 1 :=
  (intervalIntegrable_spectralGaugeSource38 z (fundContP φ z) i j).add
    (intervalIntegrable_triple_entry φ ((continuous_freeE z).comp continuous_neg)
      (continuous_ext38 (fundSpectralResolvent38 φ z)) i j)

theorem fundSpectralResolvent38_volterra (φ : PotPair) (z : ℂ) :
    fundSpectralResolvent38 φ z = spectralForcingCLM38 z (fundContP φ z) +
      volterraP φ z (fundSpectralResolvent38 φ z) := by
  have hw := fundSpectralResolvent38_source φ z
  linear_combination hw

theorem fundSpectral_gauge38 (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    fundSpectralResolvent38 φ z t i j = freeE z t i i *
      ((0 : PairMat38) i j + ∫ s in (0 : ℝ)..(t : ℝ), spectralVariationGauge38 φ z s i j) := by
  have heq := congrArg (fun F : PairCont38 => F t i j) (fundSpectralResolvent38_volterra φ z)
  simp only [ContinuousMap.add_apply, Pi.add_apply] at heq
  rw [heq, spectralForcingCLM38_apply, volterraP_apply, volterraFun_eq, freeE_mul_apply,
    Matrix.zero_apply, zero_add]
  simp only [spectralVariationGauge38, Matrix.of_apply, volterraKer]
  have hi1 := (intervalIntegrable_spectralGaugeSource38 z (fundContP φ z) i j).mono_set
    (uIcc_zero_subset t.2)
  have hi2 : IntervalIntegrable (fun s =>
      (freeE z (-s) * potCoeff38 φ s * ext38 (fundSpectralResolvent38 φ z) s) i j)
      volume 0 (t : ℝ) := by
    simpa only [Function.comp_def] using
      (intervalIntegrable_triple_entry φ ((continuous_freeE z).comp continuous_neg)
        (continuous_ext38 (fundSpectralResolvent38 φ z)) i j).mono_set (uIcc_zero_subset t.2)
  exact k1WeightedIntegralAdd38 _ _ _ _ hi1 hi2

theorem ac_fundSpectral_entry38 (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun s => ext38 (fundSpectralResolvent38 φ z) s i j) 0 1 :=
  ac_gaugePrimitive38 _ z 0 (spectralVariationGauge38 φ z)
    (intervalIntegrable_spectralVariationGauge38 φ z) (fundSpectral_gauge38 φ z) i j

theorem fundSpectral_zero_time38 (φ : PotPair) (z : ℂ) :
    fundSpectralResolvent38 φ z ⟨0, le_rfl, zero_le_one⟩ = 0 := by
  ext i j
  rw [fundSpectral_gauge38]
  simp

theorem spectralGauge_cancel38 (z : ℂ) (N : PairCont38) (s : ℝ) (i j : Fin 2) :
    freeE z s i i * spectralGaugeSource38 z N s i j =
      (spectralCoeff38 * ext38 N s) i j := by
  rw [spectralGaugeSource38, mul_assoc, freeE_mul_apply, ← mul_assoc,
    freeE_mul_freeE_neg, one_mul]

theorem ae_hasDerivAt_fundSpectral_entry38 (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun r => ext38 (fundSpectralResolvent38 φ z) r i j)
        ((zsCoeffPot38 φ z s * ext38 (fundSpectralResolvent38 φ z) s +
          spectralCoeff38 * ext38 (fundContP φ z) s) i j) s := by
  filter_upwards [ae_hasDerivAt_gaugePrimitive38 (fundSpectralResolvent38 φ z) z 0
    (spectralVariationGauge38 φ z) (intervalIntegrable_spectralVariationGauge38 φ z)
    (fundSpectral_gauge38 φ z) i j] with s hs hm
  apply (hs hm).congr_deriv
  have hφ := gaugeDeriv_coeff38 φ z s (ext38 (fundSpectralResolvent38 φ z) s) i j
  have hZ := spectralGauge_cancel38 z (fundContP φ z) s i j
  simp only [spectralVariationGauge38, Matrix.of_apply, Matrix.add_apply]
  linear_combination hφ + hZ

end
end NlsGge.GK38
