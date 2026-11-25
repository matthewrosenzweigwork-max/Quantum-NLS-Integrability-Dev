import NlsGge.GK38.GradFundamentalSpectralOp

/-! # K1: the actual shifted spectral Volterra equation.
GK Chapter I, Proposition3.1. Actual time AC and a.e. ODE precede the base-z
integrating factor and FTC. Arbitrary complex spectral shifts are retained.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory Set
namespace NlsGge.GK38
noncomputable section

 theorem k1GaugeScalarNormalize38 (a b c x y w : ℂ) (hb : b = a * c) :
    a * (c + (x + w * y)) = b + a * x + w * (a * y) := by
  rw [hb]
  ring

def shiftedSpectralGauge38 (φ : PotPair) (z w : ℂ) (s : ℝ) : PairMat38 :=
  Matrix.of fun i j =>
    (freeE z (-s) * potCoeff38 φ s * ext38 (fundContP φ (z + w)) s) i j +
      w * spectralGaugeSource38 z (fundContP φ (z + w)) s i j

theorem intervalIntegrable_shiftedSpectralGauge38 (φ : PotPair) (z w : ℂ) (i j : Fin 2) :
    IntervalIntegrable (fun s => shiftedSpectralGauge38 φ z w s i j) volume 0 1 := by
  exact ((intervalIntegrable_triple_entry φ ((continuous_freeE z).comp continuous_neg)
    (continuous_ext38 (fundContP φ (z + w))) i j).add
      ((intervalIntegrable_spectralGaugeSource38 z (fundContP φ (z + w)) i j).const_mul w))

theorem hasDerivAt_shiftedSpectralGauge38 (φ : PotPair) (z w : ℂ)
    (G : ℝ → PairMat38) (s : ℝ) (i j : Fin 2)
    (hG : HasDerivAt (fun r => G r i j) ((zsCoeffPot38 φ (z + w) s * G s) i j) s) :
    HasDerivAt (fun r => freeE z (-r) i i * G r i j)
      ((freeE z (-s) * potCoeff38 φ s * G s) i j +
        w * (freeE z (-s) * spectralCoeff38 * G s) i j) s := by
  apply ((hasDerivAt_freeE_neg_diag38 z i s).mul hG).congr_deriv
  fin_cases i <;> fin_cases j <;>
    simp [freeE, diagExp38, zsCoeffPot38, zsCoeffPair, potCoeff38,
      spectralCoeff38, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

theorem fundContP_shiftedGauge38 (φ : PotPair) (z w : ℂ)
    (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    fundContP φ (z + w) t i j = freeE z t i i *
      ((1 : PairMat38) i j + ∫ s in (0 : ℝ)..(t : ℝ), shiftedSpectralGauge38 φ z w s i j) := by
  let F : ℝ → ℂ := fun s => freeE z (-s) i i * ext38 (fundContP φ (z + w)) s i j
  have hE : AbsolutelyContinuousOnInterval (fun s : ℝ => freeE z (-s) i i) 0 1 :=
    (contDiff_freeE_neg_diag38 z i).contDiffOn.absolutelyContinuousOnInterval
  have hAC : AbsolutelyContinuousOnInterval F 0 1 := by
    convert! hE.smul (ac_fundContP_entry38 φ (z + w) i j) using 1
  have hD : ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      HasDerivAt F (shiftedSpectralGauge38 φ z w s i j) s := by
    filter_upwards [ae_hasDerivAt_fundContP_entry38 φ (z + w) i j] with s hs hm
    exact hasDerivAt_shiftedSpectralGauge38 φ z w _ s i j (hs hm)
  have hFTC := ac_integral_eq_sub38 hAC (intervalIntegrable_shiftedSpectralGauge38 φ z w i j) hD t
  have hM0 : ext38 (fundContP φ (z + w)) (0 : ℝ) = 1 :=
    (k1FundContEndpoint38 φ (z + w) ⟨0, le_rfl, zero_le_one⟩).trans (fundPair_zero _ _)
  have hF0 : F 0 = (1 : PairMat38) i j := by
    change freeE z (-(0 : ℝ)) i i * ext38 (fundContP φ (z + w)) (0 : ℝ) i j = _
    rw [neg_zero, freeE_zero, hM0]
    simp
  change (∫ s in (0 : ℝ)..(t : ℝ), shiftedSpectralGauge38 φ z w s i j) =
    freeE z (-(t : ℝ)) i i * ext38 (fundContP φ (z + w)) t i j - F 0 at hFTC
  rw [hF0, ext38_of_mem _ t.2] at hFTC
  have hu := freeE_mul_freeE_neg z (t : ℝ) i
  linear_combination -(fundContP φ (z + w) t i j) * hu - (freeE z t i i) * hFTC

/-- The true shifted solution satisfies the inhomogeneous base-z equation. -/
theorem fundContP_shiftedVolterra38 (φ : PotPair) (z w : ℂ) :
    fundContP φ (z + w) = freeFundP z + volterraP φ z (fundContP φ (z + w)) +
      w • spectralForcingCLM38 z (fundContP φ (z + w)) := by
  ext t i j
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [fundContP_shiftedGauge38, volterraP_apply, volterraFun_eq, freeE_mul_apply,
    spectralForcingCLM38_apply]
  change freeE z t i i * ((1 : PairMat38) i j + ∫ s in (0 : ℝ)..(t : ℝ),
    shiftedSpectralGauge38 φ z w s i j) = freeE z t i j +
      freeE z t i i * (∫ s in (0 : ℝ)..(t : ℝ),
        (freeE z (-s) * potCoeff38 φ s * ext38 (fundContP φ (z + w)) s) i j) +
        w * (freeE z t i i * ∫ s in (0 : ℝ)..(t : ℝ),
          spectralGaugeSource38 z (fundContP φ (z + w)) s i j)
  have hi1 : IntervalIntegrable (fun s =>
      (freeE z (-s) * potCoeff38 φ s * ext38 (fundContP φ (z + w)) s) i j) volume 0 (t : ℝ) := by
    simpa only [Function.comp_def] using
      (intervalIntegrable_triple_entry φ ((continuous_freeE z).comp continuous_neg)
        (continuous_ext38 (fundContP φ (z + w))) i j).mono_set (uIcc_zero_subset t.2)
  have hi2 := (intervalIntegrable_spectralGaugeSource38 z (fundContP φ (z + w)) i j).mono_set
    (uIcc_zero_subset t.2)
  simp only [shiftedSpectralGauge38, Matrix.of_apply]
  rw [intervalIntegral.integral_add hi1 (hi2.const_mul w), intervalIntegral.integral_const_mul]
  exact k1GaugeScalarNormalize38 _ _ _ _ _ _ (freeE_apply_eq z t i j)

end
end NlsGge.GK38
