import NlsGge.GK38.GradFundamentalTime

/-! # K1: actual unit-interval AC fundamental solution and variational ODE. -/
set_option autoImplicit false
open Filter Topology MeasureTheory Set
namespace NlsGge.GK38
noncomputable section

/-- Weighted interval sum, checked independently before its model application. -/
theorem k1WeightedIntegralAdd38 (a : ℂ) (f g : ℝ → ℂ) (t : ℝ)
    (hf : IntervalIntegrable f volume 0 t) (hg : IntervalIntegrable g volume 0 t) :
    a * (∫ s in (0 : ℝ)..t, f s) + a * (∫ s in (0 : ℝ)..t, g s) =
      a * (∫ s in (0 : ℝ)..t, f s + g s) := by
  rw [intervalIntegral.integral_add hf hg, mul_add]

theorem fundContP_gauge38 (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    fundContP φ z t i j = freeE z t i i *
      ((1 : PairMat38) i j + ∫ s in (0 : ℝ)..(t : ℝ), detKer38 φ z i j s) := by
  simpa only [Matrix.one_apply] using fundContP_entry_eq φ z t.2 i j

theorem ac_fundContP_entry38 (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun s => ext38 (fundContP φ z) s i j) 0 1 :=
  ac_gaugePrimitive38 (fundContP φ z) z 1
    (fun s => Matrix.of (fun i j => detKer38 φ z i j s))
    (fun i j => intervalIntegrable_detKer38 φ z i j) (fundContP_gauge38 φ z) i j

/-- Cancelling the gauge diagonal gives the exact accepted coefficient ODE. -/
theorem gaugeDeriv_coeff38 (φ : PotPair) (z : ℂ) (s : ℝ) (M : PairMat38) (i j : Fin 2) :
    diagExp38 (-z) i * M i j +
      freeE z s i i * (freeE z (-s) * potCoeff38 φ s * M) i j =
        (zsCoeffPot38 φ z s * M) i j := by
  rw [mul_assoc, freeE_mul_apply, ← mul_assoc, freeE_mul_freeE_neg, one_mul]
  fin_cases i <;> fin_cases j <;>
    simp [diagExp38, zsCoeffPot38, zsCoeffPair, potCoeff38, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem ae_hasDerivAt_fundContP_entry38 (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun r => ext38 (fundContP φ z) r i j)
        ((zsCoeffPot38 φ z s * ext38 (fundContP φ z) s) i j) s := by
  have h := ae_hasDerivAt_gaugePrimitive38 (fundContP φ z) z 1
    (fun s => Matrix.of (fun i j => detKer38 φ z i j s))
    (fun i j => intervalIntegrable_detKer38 φ z i j) (fundContP_gauge38 φ z) i j
  filter_upwards [h] with s hs hm
  exact (hs hm).congr_deriv (gaugeDeriv_coeff38 φ z s _ i j)

/-- The gauge integrand for the independent potential variation. -/
def potentialGaugeKer38 (φ : PotPair) (z : ℂ) (h : PotPair) (s : ℝ) : PairMat38 :=
  freeE z (-s) * potCoeff38 h s * ext38 (fundContP φ z) s +
    freeE z (-s) * potCoeff38 φ s * ext38 (fundPotentialResolventCLM38 φ z h) s

theorem intervalIntegrable_potentialGaugeKer38 (φ : PotPair) (z : ℂ) (h : PotPair) (i j : Fin 2) :
    IntervalIntegrable (fun s => potentialGaugeKer38 φ z h s i j) volume 0 1 :=
  (intervalIntegrable_triple_entry h ((continuous_freeE z).comp continuous_neg)
    (continuous_ext38 _) i j).add
    (intervalIntegrable_triple_entry φ ((continuous_freeE z).comp continuous_neg)
      (continuous_ext38 _) i j)

theorem fundPotential_gauge38 (φ : PotPair) (z : ℂ) (h : PotPair)
    (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    fundPotentialResolventCLM38 φ z h t i j = freeE z t i i *
      ((0 : PairMat38) i j + ∫ s in (0 : ℝ)..(t : ℝ), potentialGaugeKer38 φ z h s i j) := by
  have heq := congrArg (fun F : PairCont38 => F t i j) (fundPotentialResolventCLM38_volterra φ z h)
  simp only [ContinuousMap.add_apply, Pi.add_apply] at heq
  rw [heq, volterraP_apply, volterraP_apply, volterraFun_eq, volterraFun_eq, freeE_mul_apply,
    freeE_mul_apply]
  rw [Matrix.zero_apply, zero_add]
  simp only [potentialGaugeKer38, Matrix.add_apply, volterraKer, Matrix.of_apply]
  have hi1 : IntervalIntegrable (fun s =>
      (freeE z (-s) * potCoeff38 h s * ext38 (fundContP φ z) s) i j) volume 0 (t : ℝ) := by
    simpa only [Function.comp_def] using
      (intervalIntegrable_triple_entry h ((continuous_freeE z).comp continuous_neg)
        (continuous_ext38 (fundContP φ z)) i j).mono_set (uIcc_zero_subset t.2)
  have hi2 : IntervalIntegrable (fun s =>
      (freeE z (-s) * potCoeff38 φ s * ext38 (fundPotentialResolventCLM38 φ z h) s) i j)
        volume 0 (t : ℝ) := by
    simpa only [Function.comp_def] using
      (intervalIntegrable_triple_entry φ ((continuous_freeE z).comp continuous_neg)
        (continuous_ext38 (fundPotentialResolventCLM38 φ z h)) i j).mono_set (uIcc_zero_subset t.2)
  exact k1WeightedIntegralAdd38 _ _ _ _ hi1 hi2

theorem ac_fundPotential_entry38 (φ : PotPair) (z : ℂ) (h : PotPair) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval
      (fun s => ext38 (fundPotentialResolventCLM38 φ z h) s i j) 0 1 :=
  ac_gaugePrimitive38 _ z 0 (potentialGaugeKer38 φ z h)
    (intervalIntegrable_potentialGaugeKer38 φ z h) (fundPotential_gauge38 φ z h) i j


/-- The independent potential variation has zero initial value. -/
theorem fundPotential_zero_time38 (φ : PotPair) (z : ℂ) (h : PotPair) :
    fundPotentialResolventCLM38 φ z h ⟨0, le_rfl, zero_le_one⟩ = 0 := by
  ext i j
  rw [fundPotential_gauge38]
  simp

/-- Cancelling both gauge sources identifies the variational coefficient ODE. -/
theorem potentialGaugeDeriv_coeff38 (φ : PotPair) (z : ℂ) (h : PotPair) (s : ℝ) (i j : Fin 2) :
    diagExp38 (-z) i * ext38 (fundPotentialResolventCLM38 φ z h) s i j +
      freeE z s i i * potentialGaugeKer38 φ z h s i j =
        (zsCoeffPot38 φ z s * ext38 (fundPotentialResolventCLM38 φ z h) s +
          potCoeff38 h s * ext38 (fundContP φ z) s) i j := by
  unfold potentialGaugeKer38
  rw [Matrix.add_apply, mul_add]
  have hc : freeE z s i i *
      (freeE z (-s) * potCoeff38 h s * ext38 (fundContP φ z) s) i j =
      (potCoeff38 h s * ext38 (fundContP φ z) s) i j := by
    rw [mul_assoc, freeE_mul_apply, ← mul_assoc, freeE_mul_freeE_neg, one_mul]
  rw [hc, Matrix.add_apply]
  have hg := gaugeDeriv_coeff38 φ z s (ext38 (fundPotentialResolventCLM38 φ z h) s) i j
  linear_combination hg

theorem ae_hasDerivAt_fundPotential_entry38 (φ : PotPair) (z : ℂ) (h : PotPair) (i j : Fin 2) :
    ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun r => ext38 (fundPotentialResolventCLM38 φ z h) r i j)
        ((zsCoeffPot38 φ z s * ext38 (fundPotentialResolventCLM38 φ z h) s +
          potCoeff38 h s * ext38 (fundContP φ z) s) i j) s := by
  have hd := ae_hasDerivAt_gaugePrimitive38 _ z 0 (potentialGaugeKer38 φ z h)
    (intervalIntegrable_potentialGaugeKer38 φ z h) (fundPotential_gauge38 φ z h) i j
  filter_upwards [hd] with s hs hm
  exact (hs hm).congr_deriv (potentialGaugeDeriv_coeff38 φ z h s i j)

end
end NlsGge.GK38
