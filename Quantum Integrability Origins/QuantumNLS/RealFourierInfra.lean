import Mathlib

/-!
# Real-line Fourier infrastructure for R-064239ED (`lem:root-Hilbert-truncations`)

Mathlib has the Plancherel isometry `Lp.fourierTransformₗᵢ` only through the Schwartz extension.  Proved here
(not assumed), from `Real.fourierIntegral` / Schwartz / tempered-distribution API:
* `fourierL2_eq_integral`: for `f ∈ L¹ ∩ L²`, the `L²`-Fourier transform of `f` is a.e. the integral transform
  `𝓕 f = ∫ 𝐞(−vw) f(v) dv` (test against Schwartz functions: `integral_fourierIntegral_smul_eq_flip` on the integral
  side, `fourier_toTemperedDistribution_eq` on the `L²` side, then `ae_eq_of_integral_contDiff_smul_eq`);
* `parseval_L1L2`: `𝓕 f ∈ L²` and `∫ ‖𝓕 f‖² = ∫ ‖f‖²` for `f ∈ L¹ ∩ L²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory SchwartzMap
open scoped FourierTransform ENNReal ContDiff

namespace QuantumNLS.RealFourier

/-- For any measure, the `L²` norm squared of an `Lp` element is `∫ |f|²`. -/
theorem lp_norm_sq' {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  have H₃ := congr_arg RCLike.re (@L2.inner_def α ℂ ℂ _ _ _ _ _ f f)
  rw [← integral_re] at H₃
  · simp only [← norm_sq_eq_re_inner] at H₃
    exact H₃
  · exact L2.integrable_inner f f

/-- The `L²` Fourier transform of an `L¹ ∩ L²` function is its Fourier integral. -/
theorem fourierL2_eq_integral {f : ℝ → ℂ} (hf1 : Integrable f (volume : Measure ℝ))
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ∀ᵐ ξ : ℝ, ((𝓕 (hf2.toLp f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ = 𝓕 f ξ := by
  set fL : Lp ℂ 2 (volume : Measure ℝ) := hf2.toLp f with hfL
  have hcont : Continuous (𝓕 f) := by
    have := VectorFourier.fourierIntegral_continuous (e := Real.fourierChar) (μ := volume)
      (L := innerₗ ℝ) Real.continuous_fourierChar (by fun_prop) hf1
    exact this
  have hloc2 : LocallyIntegrable (𝓕 f) (volume : Measure ℝ) := hcont.locallyIntegrable
  have hloc1 : LocallyIntegrable ((𝓕 fL : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (volume : Measure ℝ) :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  refine ae_eq_of_integral_contDiff_smul_eq hloc1 hloc2 (fun g hg hgc => ?_)
  -- the Schwartz function `g` (complex valued)
  have hgc' : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) := hgc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hg' : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  let gS : 𝓢(ℝ, ℂ) := hgc'.toSchwartzMap hg'
  have hgS : ∀ x, gS x = ((g x : ℝ) : ℂ) := fun x => rfl
  -- left side
  have hL : ∫ x, g x • ((𝓕 fL : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x =
      ∫ x, (𝓕 gS : 𝓢(ℝ, ℂ)) x • f x := by
    have h1 : ∫ x, g x • ((𝓕 fL : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x =
        ((𝓕 fL : Lp ℂ 2 (volume : Measure ℝ)) : 𝓢'(ℝ, ℂ)) gS := by
      rw [Lp.toTemperedDistribution_apply]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp [hgS, Complex.real_smul]
    rw [h1, ← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply]
    rw [Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  -- right side
  have hR : ∫ x, g x • 𝓕 f x = ∫ x, (𝓕 gS : 𝓢(ℝ, ℂ)) x • f x := by
    have hint : Integrable (fun x => ((g x : ℝ) : ℂ)) (volume : Measure ℝ) :=
      (hg'.continuous.integrable_of_hasCompactSupport hgc')
    have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
      (μ := volume) (ν := volume) (L := innerₗ ℝ) Real.continuous_fourierChar (by fun_prop) hf1 hint
    have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
      ext x y; simp [real_inner_comm]
    rw [hflip] at key
    have e1 : ∀ ξ, g ξ • 𝓕 f ξ = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f ξ •
        ((g ξ : ℝ) : ℂ) := fun ξ => by
      rw [Complex.real_smul, smul_eq_mul, mul_comm]
      rfl
    have e2 : ∀ x, (𝓕 gS : 𝓢(ℝ, ℂ)) x • f x = f x • VectorFourier.fourierIntegral Real.fourierChar volume
        (innerₗ ℝ) (fun x => ((g x : ℝ) : ℂ)) x := fun x => by
      rw [smul_eq_mul, smul_eq_mul, mul_comm]
      rfl
    simp only [e1, e2]
    exact key
  rw [hL, hR]

/-- **Plancherel for `L¹ ∩ L²`**: `𝓕 f ∈ L²` and `∫ ‖𝓕 f‖² = ∫ ‖f‖²`. -/
theorem parseval_L1L2 {f : ℝ → ℂ} (hf1 : Integrable f (volume : Measure ℝ))
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (𝓕 f) 2 (volume : Measure ℝ) ∧ ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  set fL : Lp ℂ 2 (volume : Measure ℝ) := hf2.toLp f with hfL
  have hae := fourierL2_eq_integral hf1 hf2
  have hmem : MemLp (𝓕 f) 2 (volume : Measure ℝ) := (Lp.memLp (𝓕 fL : Lp ℂ 2 (volume : Measure ℝ))).ae_eq hae
  refine ⟨hmem, ?_⟩
  have h1 : ‖(𝓕 fL : Lp ℂ 2 (volume : Measure ℝ))‖ = ‖fL‖ := Lp.norm_fourier_eq fL
  have h2 := lp_norm_sq' (volume : Measure ℝ) (𝓕 fL : Lp ℂ 2 (volume : Measure ℝ))
  have h3 := lp_norm_sq' (volume : Measure ℝ) fL
  rw [h1] at h2
  have h4 : ∫ ξ, ‖((𝓕 fL : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ 2 = ∫ ξ, ‖𝓕 f ξ‖ ^ 2 :=
    integral_congr_ae (hae.mono fun ξ hξ => by beta_reduce; rw [hξ])
  have h5 : ∫ t, ‖(fL : ℝ → ℂ) t‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 :=
    integral_congr_ae (hf2.coeFn_toLp.mono fun t ht => by beta_reduce; rw [ht])
  rw [← h4, ← h5, ← h2, h3]

#print axioms parseval_L1L2

end QuantumNLS.RealFourier
