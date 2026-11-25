import Mathlib

/-!
# Cauchy-transform uniqueness for finite measures on `ℝ`

Source use: `ROOT_spectral_measure.tex`, `thm:root-measure`, Step 3 ("the Cauchy transform determines a finite measure:
its imaginary part is the Poisson convolution") and Steps 5-6 ("Cauchy-transform uniqueness identifies every weak limit").
This module proves the uniqueness in the following form, which suffices for the use in the proof: two finite measures on `ℝ`
whose Cauchy transforms `G_ρ(z) = ∫ (z - t)⁻¹ dρ(t)` agree on ONE horizontal line `{t + iη : t ∈ ℝ}` (any `η > 0`) are equal.
(The source argues with the Poisson kernel and the identity theorem; here the line already suffices.)

Proof: `-Im G_ρ(t + iη) = ∫ P_η(t - s) dρ(s)` with `P_η(y) = η/(η² + y²)`; the Fourier transform of `P_η` is `π e^{-η|ξ|}`
(derived from the mathlib Fourier inversion theorem applied to `e^{-η|x|}`); hence by Fubini
`∫ e^{iξt} (P_η * ρ)(t) dt = π e^{-η|ξ|} charFun ρ ξ`; equal Poisson smoothings give equal characteristic functions, and
mathlib's `Measure.ext_of_charFun` finishes.  No EXT-025 contract is involved.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped FourierTransform Real

noncomputable section

namespace QuantumNLS.CauchyUniqueness

/-- The Cauchy transform `G_ρ(z) = ∫ (z - t)⁻¹ dρ(t)` of a measure on `ℝ`. -/
def cauchyTransform (ρ : Measure ℝ) (z : ℂ) : ℂ := ∫ t : ℝ, (z - (t : ℂ))⁻¹ ∂ρ

/-- The Poisson kernel numerator `P_η(y) = η/(η² + y²)`. -/
def pk (η y : ℝ) : ℝ := η / (η ^ 2 + y ^ 2)

/-- The two-sided exponential `e^{-η|v|}` as a complex function. -/
def expAbs (η v : ℝ) : ℂ := ((Real.exp (-(η * |v|)) : ℝ) : ℂ)

lemma pk_nonneg {η : ℝ} (hη : 0 < η) (y : ℝ) : 0 ≤ pk η y := by
  unfold pk; positivity

lemma continuous_pk {η : ℝ} (hη : 0 < η) : Continuous (pk η) := by
  unfold pk
  refine continuous_const.div (by fun_prop) (fun y => by positivity)

lemma integrable_pk {η : ℝ} (hη : 0 < η) : Integrable (pk η) := by
  have h := (integrable_inv_one_add_sq.comp_mul_left' (R := η⁻¹) (inv_ne_zero hη.ne')).const_mul (η⁻¹)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [pk]
  field_simp

lemma integrable_expAbs {η : ℝ} (hη : 0 < η) : Integrable (expAbs η) := by
  have h1 : IntegrableOn (expAbs η) (Set.Iic 0) := by
    have := integrableOn_exp_mul_complex_Iic (a := (η : ℂ)) (by simpa using hη) 0
    refine this.congr_fun (fun v hv => ?_) measurableSet_Iic
    have hv' : |v| = -v := abs_of_nonpos hv
    simp only [expAbs, hv']
    rw [Complex.ofReal_exp]
    congr 1; push_cast; ring
  have h2 : IntegrableOn (expAbs η) (Set.Ioi 0) := by
    have := integrableOn_exp_mul_complex_Ioi (a := -(η : ℂ)) (by simpa using hη) 0
    refine this.congr_fun (fun v hv => ?_) measurableSet_Ioi
    have hv' : |v| = v := abs_of_pos hv
    simp only [expAbs, hv']
    rw [Complex.ofReal_exp]
    congr 1; push_cast; ring
  have := h1.union h2
  rw [Set.Iic_union_Ioi] at this
  exact integrableOn_univ.mp this

lemma continuous_expAbs (η : ℝ) : Continuous (expAbs η) := by
  unfold expAbs; fun_prop

/-- The Fourier transform of the two-sided exponential. -/
lemma fourier_expAbs {η : ℝ} (hη : 0 < η) (w : ℝ) :
    𝓕 (expAbs η) w = ((2 * η / (η ^ 2 + (2 * π * w) ^ 2) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  set a₁ : ℂ := (η : ℂ) - 2 * π * w * Complex.I with ha₁
  set a₂ : ℂ := -(η : ℂ) - 2 * π * w * Complex.I with ha₂
  have hre₁ : 0 < a₁.re := by simp [ha₁, hη]
  have hre₂ : a₂.re < 0 := by simp [ha₂, hη]
  have e1 : ∀ v : ℝ, v ≤ 0 → Complex.exp (↑(-2 * π * v * w) * Complex.I) • expAbs η v =
      Complex.exp (a₁ * v) := by
    intro v hv
    have hv' : |v| = -v := abs_of_nonpos hv
    simp only [expAbs, hv', smul_eq_mul]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [ha₁]; push_cast; ring
  have e2 : ∀ v : ℝ, 0 < v → Complex.exp (↑(-2 * π * v * w) * Complex.I) • expAbs η v =
      Complex.exp (a₂ * v) := by
    intro v hv
    have hv' : |v| = v := abs_of_pos hv
    simp only [expAbs, hv', smul_eq_mul]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [ha₂]; push_cast; ring
  have i1 : IntegrableOn (fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) • expAbs η v)
      (Set.Iic 0) :=
    (integrableOn_exp_mul_complex_Iic hre₁ 0).congr_fun (fun v hv => (e1 v hv).symm) measurableSet_Iic
  have i2 : IntegrableOn (fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) • expAbs η v)
      (Set.Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hre₂ 0).congr_fun (fun v hv => (e2 v hv).symm) measurableSet_Ioi
  rw [← intervalIntegral.integral_Iic_add_Ioi i1 i2]
  rw [setIntegral_congr_fun measurableSet_Iic (fun v hv => e1 v hv),
    setIntegral_congr_fun measurableSet_Ioi (fun v hv => e2 v hv),
    integral_exp_mul_complex_Iic hre₁, integral_exp_mul_complex_Ioi hre₂]
  have h1 : a₁ ≠ 0 := fun h => by simp [h] at hre₁
  have h2 : a₂ ≠ 0 := fun h => by simp [h] at hre₂
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hD : ((η : ℂ) ^ 2 + (2 * π * w) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < η ^ 2 + (2 * π * w) ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  push_cast
  rw [div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) hD]
  simp only [ha₁, ha₂]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-2 * (η : ℂ) * (2 * (π : ℂ) * (w : ℂ)) ^ 2) * hI

/-- **Fourier transform of the Poisson kernel**: `∫ e^{ixy} η/(η²+y²) dy = π e^{-η|x|}`. -/
lemma integral_pk_exp {η : ℝ} (hη : 0 < η) (x : ℝ) :
    ∫ y : ℝ, Complex.exp (((x * y : ℝ) : ℂ) * Complex.I) * ((pk η y : ℝ) : ℂ) = π * expAbs η x := by
  have hint : Integrable (𝓕 (expAbs η)) := by
    have : 𝓕 (expAbs η) = fun w : ℝ => ((2 * η / (η ^ 2 + (2 * π * w) ^ 2) : ℝ) : ℂ) :=
      funext (fourier_expAbs hη)
    rw [this]
    have h0 : Integrable (fun w : ℝ => 2 * η / (η ^ 2 + (2 * π * w) ^ 2)) := by
      have := ((integrable_inv_one_add_sq.comp_mul_left' (R := 2 * π / η)
        (by positivity)).const_mul (2 / η))
      refine this.congr (Filter.Eventually.of_forall fun w => ?_)
      simp only
      field_simp
    exact h0.ofReal
  have hinv := Continuous.fourierInv_fourier_eq (continuous_expAbs η) (integrable_expAbs hη) hint
  have hx := congrFun hinv x
  rw [Real.fourierInv_eq'] at hx
  simp_rw [fourier_expAbs hη] at hx
  -- hx : ∫ v, exp (↑(2π ⟪v,x⟫) I) • ↑(2η/(η²+(2πv)²)) = expAbs η x
  have hinner : ∀ v : ℝ, (inner ℝ v x : ℝ) = v * x := fun v => by simp [mul_comm]
  simp_rw [hinner, smul_eq_mul] at hx
  set g : ℝ → ℂ := fun y => Complex.exp (((x * y : ℝ) : ℂ) * Complex.I) * ((2 * pk η y : ℝ) : ℂ) with hg
  have hcomp := Measure.integral_comp_mul_left g (2 * π)
  have hg' : ∀ v : ℝ, g (2 * π * v) =
      Complex.exp (↑(2 * π * (v * x)) * Complex.I) * ((2 * η / (η ^ 2 + (2 * π * v) ^ 2) : ℝ) : ℂ) := by
    intro v
    have e1 : ((x * (2 * π * v) : ℝ) : ℂ) = ((2 * π * (v * x) : ℝ) : ℂ) := by congr 1; ring
    have e2 : (2 * pk η (2 * π * v) : ℝ) = 2 * η / (η ^ 2 + (2 * π * v) ^ 2) := by unfold pk; ring
    show Complex.exp (((x * (2 * π * v) : ℝ) : ℂ) * Complex.I) * ((2 * pk η (2 * π * v) : ℝ) : ℂ) = _
    rw [e1, e2]
  simp_rw [hg'] at hcomp
  rw [hx] at hcomp
  have hpos : (0 : ℝ) < π := Real.pi_pos
  have habs : |(2 * π)⁻¹| = (2 * π)⁻¹ := abs_of_pos (by positivity)
  rw [habs] at hcomp
  have hsplit : ∫ y : ℝ, g y = 2 * ∫ y : ℝ, Complex.exp (((x * y : ℝ) : ℂ) * Complex.I) * ((pk η y : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    congr 1; ext y
    simp only [hg]; push_cast; ring
  rw [hsplit, Complex.real_smul] at hcomp
  generalize (∫ y : ℝ, Complex.exp (((x * y : ℝ) : ℂ) * Complex.I) * ((pk η y : ℝ) : ℂ)) = J at hcomp ⊢
  rw [hcomp]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hk : (π : ℂ) * (((2 * π)⁻¹ : ℝ) : ℂ) * 2 = 1 := by
    push_cast; field_simp
  linear_combination (-J) * hk

/-- Total mass of the Poisson kernel. -/
lemma integral_pk {η : ℝ} (hη : 0 < η) : ∫ y : ℝ, pk η y = π := by
  have h := integral_pk_exp hη 0
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, expAbs, abs_zero,
    mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one] at h
  have hr : (∫ y : ℝ, ((pk η y : ℝ) : ℂ)) = ((∫ y : ℝ, pk η y : ℝ) : ℂ) := integral_ofReal
  rw [hr, mul_one] at h
  exact_mod_cast h

/-- The Poisson smoothing `(P_η * ρ)(t) = ∫ P_η(t - s) dρ(s)`. -/
def poisson (η : ℝ) (ρ : Measure ℝ) (t : ℝ) : ℝ := ∫ s : ℝ, pk η (t - s) ∂ρ

lemma integrable_cauchyKernel (ρ : Measure ℝ) [IsFiniteMeasure ρ] {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ => (z - (t : ℂ))⁻¹) ρ := by
  have hne : ∀ t : ℝ, z - (t : ℂ) ≠ 0 := fun t h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hc : Continuous (fun t : ℝ => (z - (t : ℂ))⁻¹) :=
    (continuous_const.sub Complex.continuous_ofReal).inv₀ hne
  refine Integrable.mono' (integrable_const (z.im)⁻¹) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_inv]
  have hzq : z.im ≤ ‖z - (t : ℂ)‖ := by
    have := Complex.abs_im_le_norm (z - (t : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  exact inv_anti₀ hz hzq

lemma im_cauchy (ρ : Measure ℝ) [IsFiniteMeasure ρ] {η : ℝ} (hη : 0 < η) (t : ℝ) :
    (cauchyTransform ρ ((t : ℂ) + η * Complex.I)).im = - poisson η ρ t := by
  have hz : 0 < ((t : ℂ) + η * Complex.I).im := by simpa using hη
  unfold cauchyTransform poisson
  have := integral_im (𝕜 := ℂ) (integrable_cauchyKernel ρ hz)
  simp only [RCLike.im_to_complex] at this
  rw [← this, ← integral_neg]
  congr 1; ext s
  have hD : (η ^ 2 + (t - s) ^ 2 : ℝ) ≠ 0 := by positivity
  simp only [pk]
  have h1 : ((t : ℂ) + η * Complex.I - (s : ℂ)) = (((t - s : ℝ) : ℂ) + (η : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h1, Complex.inv_im]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, mul_zero, mul_one, zero_add, Complex.normSq_apply, Complex.add_re,
    Complex.mul_re, sub_zero, add_zero]
  field_simp
  ring

/-- **Fubini step**: `∫ e^{iξt} (P_η * ρ)(t) dt = π e^{-η|ξ|} charFun ρ ξ`. -/
lemma integral_poisson_exp (ρ : Measure ℝ) [IsFiniteMeasure ρ] {η : ℝ} (hη : 0 < η) (ξ : ℝ) :
    ∫ t : ℝ, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I) * ((poisson η ρ t : ℝ) : ℂ) =
      π * expAbs η ξ * ∫ s : ℝ, Complex.exp (((ξ * s : ℝ) : ℂ) * Complex.I) ∂ρ := by
  set f : ℝ → ℝ → ℂ := fun t s => Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I) * ((pk η (t - s) : ℝ) : ℂ)
    with hf
  have hcont : Continuous (Function.uncurry f) := by
    have hc1 : Continuous fun p : ℝ × ℝ => Complex.exp (((ξ * p.1 : ℝ) : ℂ) * Complex.I) := by fun_prop
    have hc2 : Continuous fun p : ℝ × ℝ => ((pk η (p.1 - p.2) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_pk hη).comp (continuous_fst.sub continuous_snd))
    exact hc1.mul hc2
  have hnorm : ∀ t s : ℝ, ‖f t s‖ = pk η (t - s) := by
    intro t s
    simp only [hf, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (pk_nonneg hη _)]
  have hint : Integrable (Function.uncurry f) ((volume : Measure ℝ).prod ρ) := by
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun s => ?_, ?_⟩
    · have := (integrable_pk hη).comp_sub_right s
      refine Integrable.mono' this (by exact (hcont.comp (by fun_prop : Continuous fun t : ℝ => (t, s))).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.uncurry, hnorm]; exact le_rfl
    · have : (fun s : ℝ => ∫ t : ℝ, ‖Function.uncurry f (t, s)‖) = fun _ => π := by
        funext s
        simp only [Function.uncurry, hnorm]
        rw [integral_sub_right_eq_self (pk η) s, integral_pk hη]
      rw [this]; exact integrable_const _
  have hswap := integral_integral_swap hint
  have hLHS : (∫ t : ℝ, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I) * ((poisson η ρ t : ℝ) : ℂ)) =
      ∫ t : ℝ, ∫ s : ℝ, f t s ∂ρ := by
    congr 1; ext t
    simp only [hf, poisson]
    have hr : ((∫ s : ℝ, pk η (t - s) ∂ρ : ℝ) : ℂ) = ∫ s : ℝ, ((pk η (t - s) : ℝ) : ℂ) ∂ρ :=
      integral_ofReal.symm
    rw [hr, ← integral_const_mul]
  rw [hLHS, hswap]
  have hinner : ∀ s : ℝ, ∫ t : ℝ, f t s = Complex.exp (((ξ * s : ℝ) : ℂ) * Complex.I) * (π * expAbs η ξ) := by
    intro s
    have h1 : ∀ t : ℝ, f t s = Complex.exp (((ξ * s : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (((ξ * (t - s) : ℝ) : ℂ) * Complex.I) * ((pk η (t - s) : ℝ) : ℂ)) := by
      intro t
      simp only [hf]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2; push_cast; ring
    simp_rw [h1]
    rw [integral_const_mul]
    congr 1
    rw [integral_sub_right_eq_self (fun y => Complex.exp (((ξ * y : ℝ) : ℂ) * Complex.I) * ((pk η y : ℝ) : ℂ)) s]
    exact integral_pk_exp hη ξ
  simp_rw [hinner]
  rw [integral_mul_const, mul_comm]

/-- **Cauchy-transform uniqueness**: finite measures whose Cauchy transforms agree on one horizontal line are equal. -/
theorem cauchy_ext (ρ σ : Measure ℝ) [IsFiniteMeasure ρ] [IsFiniteMeasure σ] {η : ℝ} (hη : 0 < η)
    (h : ∀ t : ℝ, cauchyTransform ρ ((t : ℂ) + η * Complex.I) =
      cauchyTransform σ ((t : ℂ) + η * Complex.I)) : ρ = σ := by
  have hP : ∀ t, poisson η ρ t = poisson η σ t := by
    intro t
    have := congrArg Complex.im (h t)
    rw [im_cauchy ρ hη, im_cauchy σ hη] at this
    linarith
  apply Measure.ext_of_charFun
  funext ξ
  have h1 := integral_poisson_exp ρ hη ξ
  have h2 := integral_poisson_exp σ hη ξ
  have h3 : π * expAbs η ξ * ∫ s : ℝ, Complex.exp (((ξ * s : ℝ) : ℂ) * Complex.I) ∂ρ =
      π * expAbs η ξ * ∫ s : ℝ, Complex.exp (((ξ * s : ℝ) : ℂ) * Complex.I) ∂σ := by
    rw [← h1, ← h2]
    simp_rw [hP]
  have hne : (π : ℂ) * expAbs η ξ ≠ 0 := by
    have : expAbs η ξ ≠ 0 := by
      unfold expAbs
      exact_mod_cast (Real.exp_pos _).ne'
    exact mul_ne_zero (by exact_mod_cast Real.pi_pos.ne') this
  have h4 := mul_left_cancel₀ hne h3
  simp only [charFun_apply_real]
  push_cast at h4 ⊢
  exact h4

end QuantumNLS.CauchyUniqueness

#print axioms QuantumNLS.CauchyUniqueness.fourier_expAbs
#print axioms QuantumNLS.CauchyUniqueness.integral_pk_exp
#print axioms QuantumNLS.CauchyUniqueness.im_cauchy
#print axioms QuantumNLS.CauchyUniqueness.integral_poisson_exp
#print axioms QuantumNLS.CauchyUniqueness.cauchy_ext
