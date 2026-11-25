import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB2CutoffKernel

/-! # Track B, step B2: the summed dense-class cutoff gain

For a time-side Schwartz cutoff `η` and `δ > 0` put `η_δ(t) = η(t/δ)` (`dilateS η δ`). The change
of variables `t = δu` in the inverse Fourier integral gives `𝓕⁻ η_δ (r) = δ (𝓕⁻ η)(δ r)`
(`fourierInv_dilateS`). For a dense-class field with time-Schwartz modes `s_k`, the cut-off field
has modes `η_δ s_k` (`cutMul`), and `𝓕⁻(η_δ s_k) = 𝓕⁻ η_δ ⋆ 𝓕⁻ s_k` (Schwartz convolution theorem).
Summing the uniform one-mode gain `cutoff_gain_dilated` over `k` yields, for
`0 ≤ α ≤ β < 1/2`, `0 < β`,
`‖η_δ v‖²_{X^{0,-β}} ≤ C δ^{2β-2α} ‖v‖²_{X^{0,-α}}` uniformly in `δ > 0` and the dense field `v`.
All norms are the `ℝ≥0∞` dense-class norms `denseNormSqE`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory SchwartzMap FourierTransform
open scoped ENNReal

/-- Pointwise product of two time-side Schwartz functions (as a Schwartz function). -/
def cutMul (c f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) c f

theorem cutMul_apply (c f : 𝓢(ℝ, ℂ)) (t : ℝ) : cutMul c f t = c t * f t := by
  simp [cutMul, pairing_apply_apply]

/-- The dilated cutoff `η_δ(t) = η(t/δ)` (and `0` for the excluded value `δ = 0`). -/
def dilateS (η : 𝓢(ℝ, ℂ)) (δ : ℝ) : 𝓢(ℝ, ℂ) :=
  if h : δ = 0 then 0 else
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 δ⁻¹ (inv_ne_zero h))) η

theorem dilateS_apply (η : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : δ ≠ 0) (t : ℝ) :
    dilateS η δ t = η (t / δ) := by
  simp [dilateS, hδ, div_eq_mul_inv]

/-- Change of variables: `𝓕⁻(η(·/δ))(r) = δ (𝓕⁻ η)(δ r)`. -/
theorem fourierInv_dilateS (η : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    (𝓕⁻ (dilateS η δ) : 𝓢(ℝ, ℂ)) r = (δ : ℂ) * (𝓕⁻ η : 𝓢(ℝ, ℂ)) (δ * r) := by
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe, Real.fourierInv_eq',
    Real.fourierInv_eq']
  have h := Measure.integral_comp_mul_left
    (fun v : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ v r) * Complex.I) • (dilateS η δ) v) δ
  have hF : ∀ x : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ (δ * x) r) * Complex.I) •
      (dilateS η δ) (δ * x) =
      Complex.exp (↑(2 * Real.pi * inner ℝ x (δ * r)) * Complex.I) • η x := fun x => by
    rw [dilateS_apply η hδ.ne', mul_div_cancel_left₀ x hδ.ne']
    congr 4
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  simp only [hF] at h
  rw [h, abs_of_pos (inv_pos.2 hδ), Complex.real_smul, ← mul_assoc, Complex.ofReal_inv,
    mul_inv_cancel₀ (by exact_mod_cast hδ.ne'), one_mul]

/-- The inverse transform of a product is bounded by the convolution of the moduli. -/
theorem enorm_fourierInv_cutMul_le (c f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    ‖(𝓕⁻ (cutMul c f) : 𝓢(ℝ, ℂ)) ξ‖ₑ ≤
      ∫⁻ ζ, ‖(𝓕⁻ c : 𝓢(ℝ, ℂ)) (ξ - ζ)‖ₑ * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ζ‖ₑ := by
  have h1 : cutMul c f =
      𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ c) (𝓕⁻ f)) := by
    ext t
    rw [cutMul_apply]
    exact mul_eq_fourier_convolution c f t
  rw [h1, FourierTransform.fourierInv_fourier_eq, SchwartzMap.convolution_apply, convolution_def]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  rw [← lintegral_sub_left_eq_self _ ξ]
  congr 1
  funext ζ
  simp [enorm_mul, sub_sub_cancel]

/-- One mode: the weighted `L²` norm of `𝓕⁻(c f)` is dominated by that of the convolution bound. -/
theorem lintegral_cutMul_le (c f : 𝓢(ℝ, ℂ)) (e : ℝ) (k : ℤ) :
    ∫⁻ ξ, modWt e k (-(2 * Real.pi) * ξ) * ‖(𝓕⁻ (cutMul c f) : 𝓢(ℝ, ℂ)) ξ‖ₑ ^ 2 ≤
      ∫⁻ ξ, modWt e k (-(2 * Real.pi) * ξ) *
        (∫⁻ ζ, ‖(𝓕⁻ c : 𝓢(ℝ, ℂ)) (ξ - ζ)‖ₑ * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ζ‖ₑ) ^ 2 :=
  lintegral_mono fun ξ => by
    gcongr
    exact enorm_fourierInv_cutMul_le c f ξ

/-- **Summed dense-class cutoff gain.** For `0 ≤ α ≤ β < 1/2`, `0 < β`, and a Schwartz cutoff `η`,
there is `C < ∞` such that for every `δ > 0` and every family of time-Schwartz modes `s`,
`‖η(·/δ) v‖²_{X^{0,-β}} ≤ C δ^{2β-2α} ‖v‖²_{X^{0,-α}}` (dense-class norms). -/
theorem dense_cutoff_gain {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ0 : 0 < β) (hβ : β < 1 / 2)
    (η : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → ∀ s : ℤ → 𝓢(ℝ, ℂ),
      denseNormSqE (-(2 * β)) (fun k => cutMul (dilateS η δ) (s k)) ≤
        C * ENNReal.ofReal (δ ^ (2 * β - 2 * α)) * denseNormSqE (-(2 * α)) s := by
  obtain ⟨C, hC, h⟩ := cutoff_gain_dilated hα hαβ hβ0 hβ (𝓕⁻ η : 𝓢(ℝ, ℂ))
  refine ⟨C, hC, fun δ hδ s => ?_⟩
  unfold denseNormSqE
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  refine (lintegral_cutMul_le _ _ _ _).trans ?_
  simp_rw [fourierInv_dilateS η hδ]
  exact h δ hδ _ (𝓕⁻ (s k) : 𝓢(ℝ, ℂ)).continuous.measurable k

/-- The cut-off dense field is the pointwise product with `η(t/δ)`. -/
theorem denseField_cutMul (η : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : δ ≠ 0) (S : Finset ℤ)
    (s : ℤ → 𝓢(ℝ, ℂ)) (t : ℝ) (x : AddCircle (1 : ℝ)) :
    denseField S (fun k => cutMul (dilateS η δ) (s k)) t x = η (t / δ) * denseField S s t x := by
  simp only [denseField, torusPoly_apply, cutMul_apply, dilateS_apply η hδ, Finset.mul_sum,
    mul_assoc]

end LiebLiniger.FixedPeriod.ALLS.PdeB
