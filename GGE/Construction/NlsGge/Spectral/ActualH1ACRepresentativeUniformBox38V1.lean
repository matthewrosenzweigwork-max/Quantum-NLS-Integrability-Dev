import NlsGge.Analysis.H1Fourier
import NlsGge.Spectral.ActualPhysicalUnitRawCoverNorm32V1
import NlsGge.Spectral.ComplexIntervalIntegralPrimitiveAbsolutelyContinuousV2
import NlsGge.Schur.SourceSubintervalIntegralPairingCLMV5
import NlsGge.Spectral.ActualL2PotentialTimesLInfStateV1

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

theorem uA_physical_ae_pullback_first_half {a b : PhysicalCircle → ℂ}
    (h : a =ᵐ[spatialMeasure] b) :
    (fun x : ℝ => a (x : PhysicalCircle)) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun x : ℝ => b (x : PhysicalCircle)) := by
  have h1 : (fun x : SpectralCircle => a (naturalPhysicalCover x)) =ᵐ[spectralHaar]
      (fun x => b (naturalPhysicalCover x)) :=
    naturalPhysicalCover_preserving.quasiMeasurePreserving.ae_eq_comp h
  simpa only [naturalPhysicalCover_coe] using spectral_ae_pullback_first_half h1

def uA_A : PhysicalL2 →ₗᵢ[ℂ] SourceIntervalL2 where
  toFun := actualPhysicalL2SourcePotential
  map_add' a b := by
    have h : (⟨naturalPhysicalCoverL2 (a + b), naturalPhysicalCoverL2_mem_even (a + b)⟩ :
        scalarParity 0) = ⟨naturalPhysicalCoverL2 a, naturalPhysicalCoverL2_mem_even a⟩ +
        ⟨naturalPhysicalCoverL2 b, naturalPhysicalCoverL2_mem_even b⟩ :=
      Subtype.ext (map_add _ a b)
    unfold actualPhysicalL2SourcePotential
    rw [h, map_add]
  map_smul' c a := by
    have h : (⟨naturalPhysicalCoverL2 (c • a), naturalPhysicalCoverL2_mem_even (c • a)⟩ :
        scalarParity 0) = c • ⟨naturalPhysicalCoverL2 a, naturalPhysicalCoverL2_mem_even a⟩ :=
      Subtype.ext (map_smul _ c a)
    unfold actualPhysicalL2SourcePotential
    rw [h, map_smul]
    rfl
  norm_map' := actualPhysicalL2SourcePotential_norm

theorem uA_A_apply (u : PhysicalL2) : uA_A u = actualPhysicalL2SourcePotential u := rfl

theorem uA_continuous_rep_ae (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    (fun t : ℝ => physicalH1Continuous u hu (t : PhysicalCircle)) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun x : ℝ => naturalPhysicalCoverL2 u (x : SpectralCircle)) := by
  have h1 : (u : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] (physicalH1Continuous u hu : PhysicalCircle → ℂ) := by
    have := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure (physicalH1Continuous u hu)
    rw [physicalH1Continuous_toLp u hu] at this
    exact this
  have h2 := uA_physical_ae_pullback_first_half h1
  have h3 := actualPhysicalL2SourcePotential_ae u
  have h4 := actualPhysicalSourcePotential_rawCover_ae32 u
  filter_upwards [h2, h3, h4] with x hx2 hx3 hx4
  rw [← hx2, ← hx3, hx4]

/-- Fourier coefficients `2π i n û_n` of the distributional derivative. -/
def uA_coeff (u : PhysicalL2) (n : ℤ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * physicalFourier u n

theorem uA_sobolev_weight (n : ℤ) :
    Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) = 1 + (n : ℝ) ^ 2 :=
  japaneseBracket_h1_weight n

theorem uA_coeff_norm_sq_le (u : PhysicalL2) (n : ℤ) :
    ‖uA_coeff u n‖ ^ 2 ≤
      (2 * Real.pi) ^ 2 * (Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) * ‖physicalFourier u n‖ ^ 2) := by
  rw [uA_sobolev_weight]
  have h : ‖uA_coeff u n‖ ^ 2 = (2 * Real.pi) ^ 2 * ((n : ℝ) ^ 2 * ‖physicalFourier u n‖ ^ 2) := by
    have hm : ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))‖ = 2 * Real.pi * |(n : ℝ)| := by
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
    unfold uA_coeff
    rw [norm_mul, hm, mul_pow, mul_pow, sq_abs]
    ring
  rw [h]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [sq_nonneg ‖physicalFourier u n‖]

theorem uA_coeff_summable (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun n : ℤ => (fun _ : ℤ => (1 : ℝ)) n * ‖uA_coeff u n‖ ^ 2) := by
  have h := hu.mul_left ((2 * Real.pi) ^ 2)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h
  simpa using uA_coeff_norm_sq_le u n

def uA_derivL2 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) : lp (fun _ : ℤ => ℂ) 2 :=
  weightedL2Element (fun _ => 1) (fun _ => zero_le_one) (uA_coeff u) (uA_coeff_summable u hu)

theorem uA_derivL2_apply (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    uA_derivL2 u hu n = uA_coeff u n := by
  simp [uA_derivL2, weightedL2Element, weightedCoordinates]

def uA_deriv (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) : PhysicalL2 :=
  physicalFourierL2.symm (uA_derivL2 u hu)

theorem uA_deriv_fourier (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    physicalFourier (uA_deriv u hu) n = uA_coeff u n := by
  rw [← physicalFourierL2_apply]
  simp [uA_deriv, uA_derivL2_apply]

theorem uA_deriv_norm_le (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖uA_deriv u hu‖ ≤ 2 * Real.pi * ‖physicalSobolevL2 1 u hu‖ := by
  have h1 : ‖uA_deriv u hu‖ = ‖uA_derivL2 u hu‖ := by
    simp [uA_deriv]
  rw [h1]
  have hsq : ‖uA_derivL2 u hu‖ ^ 2 ≤ (2 * Real.pi * ‖physicalSobolevL2 1 u hu‖) ^ 2 := by
    rw [uA_derivL2, weightedL2Element_norm_sq, mul_pow, physicalSobolevL2_norm_sq, ← tsum_mul_left]
    apply Summable.tsum_le_tsum (fun n => ?_) (uA_coeff_summable u hu) (hu.mul_left _)
    simpa using uA_coeff_norm_sq_le u n
  exact le_of_sq_le_sq hsq (by positivity)

/-- Source-interval integral functional composed with the actual representative map. -/
def uA_Q (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : PhysicalL2 →L[ℂ] ℂ :=
  (sourceSubintervalIntegralCLM t ht).comp uA_A.toContinuousLinearMap

theorem uA_Q_apply (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (w : PhysicalL2) :
    uA_Q t ht w = ∫ x in (0 : ℝ)..t, actualPhysicalL2SourcePotential w x := by
  simp [uA_Q, sourceSubintervalIntegralCLM_apply, uA_A_apply]

/-- The `n`-th period-one Fourier character as an element of `PhysicalL2`. -/
def uA_e (n : ℤ) : PhysicalL2 := fourierLp (T := (1 : ℝ)) 2 n

theorem uA_Q_fourier (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (n : ℤ) :
    uA_Q t ht (uA_e n) =
      ∫ x in (0 : ℝ)..t, Complex.exp (2 * Real.pi * Complex.I * n * x) := by
  rw [uA_Q_apply]
  have h1 := uA_physical_ae_pullback_first_half
    (coeFn_fourierLp (T := (1 : ℝ)) 2 n)
  have h2 := actualPhysicalL2SourcePotential_ae (uA_e n)
  have h3 : (actualPhysicalL2SourcePotential (uA_e n) : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)] fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * n * x) := by
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx2]
    change (fourierLp (T := (1 : ℝ)) 2 n : PhysicalCircle → ℂ) (x : PhysicalCircle) = _
    rw [hx1, fourier_coe_apply]
    simp
  rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
  apply integral_congr_ae
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Ioc (0 : ℝ) 1 := Set.Ioc_subset_Ioc le_rfl ht.2
  exact ae_restrict_of_ae_restrict_of_subset hsub h3

theorem uA_term_eq (u : PhysicalL2) (t : ℝ) (n : ℤ) :
    uA_coeff u n * (∫ x in (0 : ℝ)..t, Complex.exp (2 * Real.pi * Complex.I * n * x)) =
      physicalFourier u n * (Complex.exp (2 * Real.pi * Complex.I * n * t) -
        Complex.exp (2 * Real.pi * Complex.I * n * (0 : ℝ))) := by
  by_cases hn : n = 0
  · subst hn
    simp [uA_coeff]
  · have hc : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    rw [integral_exp_mul_complex (by simpa [mul_assoc] using hc)]
    unfold uA_coeff
    field_simp

theorem uA_integral_deriv (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..t, actualPhysicalL2SourcePotential (uA_deriv u hu) x =
      physicalH1Continuous u hu (t : PhysicalCircle) -
        physicalH1Continuous u hu ((0 : ℝ) : PhysicalCircle) := by
  have hv : HasSum (fun i : ℤ => fourierCoeff (uA_deriv u hu) i • uA_e i) (uA_deriv u hu) :=
    hasSum_fourier_series_L2 (T := (1 : ℝ)) (uA_deriv u hu)
  have hQ := hv.mapL (uA_Q t ht)
  have hF := physicalH1Continuous_hasSum u hu
  have hFt := (ContinuousMap.hasSum_apply hF (t : PhysicalCircle))
  have hF0 := (ContinuousMap.hasSum_apply hF ((0 : ℝ) : PhysicalCircle))
  have hdiff := hFt.sub hF0
  rw [← uA_Q_apply]
  refine hQ.unique ?_
  convert hdiff using 1
  funext n
  simp only [map_smul, smul_eq_mul, uA_Q_fourier]
  have e1 : fourierCoeff (uA_deriv u hu) n = uA_coeff u n := uA_deriv_fourier u hu n
  rw [e1, uA_term_eq]
  simp
  ring

theorem uA_const_absolutelyContinuous (c : ℂ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 1 :=
  (contDiffOn_const (c := c) (n := 1) (s := Set.uIcc (0 : ℝ) 1)).absolutelyContinuousOnInterval

theorem uA_l1_le_l2 (w : SourceIntervalL2) :
    ∫ x in (0 : ℝ)..1, ‖w x‖ ≤ ‖w‖ := by
  let μ₁ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have : IsFiniteMeasure μ₁ := Real.isFiniteMeasure_restrict_Ioc 0 1
  have hw : MemLp (fun x : ℝ => ‖w x‖) (ENNReal.ofReal 2) μ₁ := by
    simpa using (Lp.memLp w).norm
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ₁ := memLp_const 1
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ₁) (p := 2) (q := 2) (by rw [Real.holderConjugate_iff]; norm_num)
    (Filter.Eventually.of_forall (fun x => norm_nonneg (w x)))
    (Filter.Eventually.of_forall (fun _ => zero_le_one)) hw h1
  have hsq : ∫ x, ‖w x‖ ^ (2 : ℝ) ∂μ₁ = ‖w‖ ^ 2 := by
    simp only [Real.rpow_two]
    exact (sourceInterval_norm_sq w).symm
  have hone : ∫ x, (1 : ℝ) ^ (2 : ℝ) ∂μ₁ = 1 := by
    simp [μ₁]
  rw [hsq, hone] at hcs
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have h2 : (‖w‖ ^ 2) ^ (1 / (2 : ℝ)) = ‖w‖ := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_sq (norm_nonneg _)
  rw [h2] at hcs
  simpa [μ₁] using hcs

theorem uA_deriv_intervalIntegrable (w : SourceIntervalL2) :
    IntervalIntegrable (fun x : ℝ => w x) volume 0 1 := by
  let μ₁ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have : IsFiniteMeasure μ₁ := Real.isFiniteMeasure_restrict_Ioc 0 1
  have hU : Integrable (w : ℝ → ℂ) μ₁ :=
    (Lp.memLp w).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa only [IntegrableOn, μ₁] using hU

/-- Uniform `H¹` absolutely continuous representative on the unit box.

Interpretation: `PhysicalL2` is the period-one `L²` space, `physicalFourier u n` the
coefficient `∫ e^{-2πinx} u`, and `physicalSobolevL2 1 u hu` the `ℓ²` element with
`‖·‖² = ∑ (1+n²)|û_n|²`. `f` is the (period-one) continuous Fourier-series representative
`∑ û_n e^{2πint}` restricted to `ℝ`, `f'` the `L²` derivative with Fourier coefficients
`2πi n û_n`, represented on `(0,1]` via the actual source-interval potential map. The
a.e. identification is with the actual representative `naturalPhysicalCoverL2 u` on the
doubled circle restricted to `(0,1]`. Constants: `Cinf = ‖reciprocalBracketL2‖ + 1`,
`C₁ = 2π`; they depend on nothing. -/
theorem actualH1ACRepresentativeUniformBox38V1 :
    ∃ Cinf C₁ : ℝ, 0 < Cinf ∧ 0 < C₁ ∧
      ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
        ∃ f f' : ℝ → ℂ,
          AbsolutelyContinuousOnInterval f 0 1 ∧
          IntervalIntegrable f' volume 0 1 ∧
          (∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 → HasDerivAt f (f' t) t) ∧
          f =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
            (fun x : ℝ => naturalPhysicalCoverL2 u (x : SpectralCircle)) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f t‖ ≤ Cinf * ‖physicalSobolevL2 1 u hu‖) ∧
          ∫ t in (0 : ℝ)..1, ‖f' t‖ ≤ C₁ * ‖physicalSobolevL2 1 u hu‖ := by
  refine ⟨‖reciprocalBracketL2‖ + 1, 2 * Real.pi, by positivity, by positivity, ?_⟩
  intro u hu
  let F := physicalH1Continuous u hu
  let f : ℝ → ℂ := fun t => F (t : PhysicalCircle)
  let g : ℝ → ℂ := fun x => actualPhysicalL2SourcePotential (uA_deriv u hu) x
  have hI : IntervalIntegrable g volume 0 1 := uA_deriv_intervalIntegrable _
  have hprim : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = f 0 + ∫ s in (0 : ℝ)..t, g s := by
    intro t ht
    have h := uA_integral_deriv u hu t ht
    simp only [f, g]
    rw [h]; ring
  refine ⟨f, g, ?_, hI, ?_, uA_continuous_rep_ae u hu, ?_, ?_⟩
  · have hp := NlsGge.SpectralFoundations.complex_intervalIntegral_primitive_absolutelyContinuousV2 hI
      (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1)
    have hs := (uA_const_absolutelyContinuous (f 0)).add hp
    refine hs.congr ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact (hprim t ht).symm
  · have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff, measure_singleton]
    have h1 : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by simp [ae_iff, measure_singleton]
    filter_upwards [hI.ae_hasDerivAt_integral, h0, h1] with x hx hx0 hx1 hmem
    have hd := (hx hmem 0 (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1)).const_add (f 0)
    refine hd.congr_of_eventuallyEq ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hmem
    have hmem' : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hx0), lt_of_le_of_ne hmem.2 hx1⟩
    filter_upwards [Ioo_mem_nhds hmem'.1 hmem'.2] with y hy
    exact hprim y ⟨hy.1.le, hy.2.le⟩
  · intro t _
    calc ‖f t‖ ≤ ‖F‖ := ContinuousMap.norm_coe_le_norm F _
      _ ≤ ‖physicalSobolevL2 1 u hu‖ * ‖reciprocalBracketL2‖ := physicalH1Continuous_norm_bound u hu
      _ ≤ (‖reciprocalBracketL2‖ + 1) * ‖physicalSobolevL2 1 u hu‖ := by
        nlinarith [norm_nonneg (physicalSobolevL2 1 u hu), norm_nonneg reciprocalBracketL2]
  · calc ∫ t in (0 : ℝ)..1, ‖g t‖ ≤ ‖actualPhysicalL2SourcePotential (uA_deriv u hu)‖ :=
          uA_l1_le_l2 _
      _ = ‖uA_deriv u hu‖ := actualPhysicalL2SourcePotential_norm _
      _ ≤ 2 * Real.pi * ‖physicalSobolevL2 1 u hu‖ := uA_deriv_norm_le u hu

end NlsGge.Schur
end
