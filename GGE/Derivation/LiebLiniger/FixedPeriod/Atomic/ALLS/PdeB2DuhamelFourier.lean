import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB2DuhamelSchwartz

/-! # Track B, step B2: the inverse Fourier transform of the fixed-cutoff Duhamel output

For Schwartz `η`, `g` and `λ ∈ ℝ`, with `θ = 𝓕⁻ g` and `Ψ = 𝓕⁻ η`:
`𝓕⁻(η(t) ∫₀ᵗ e^{-iλ(t-r)} g(r) dr)(ξ) = ∫ θ(ζ) K(ξ - λ/2π, ζ - λ/2π) dζ`,
`K = duhKer Ψ`, hence `|𝓕⁻(duhOut η λ g)(ξ)| ≤ ∫ |K(ξ - λ/2π, z)| |θ(z + λ/2π)| dz`.
Proof: Fourier inversion `g = 𝓕 θ`; Fubini on `[0,t] × ℝ` (finite measure, `|θ| ∈ L¹`);
the closed form `∫₀ᵗ e^{-iλ(t-r)} e^{-2πiζr} dr = (e^{-iλt} - e^{-2πiζt})/(i(2πζ - λ))` for `2πζ ≠ λ`;
Fubini on `ℝ × ℝ` with the majorant `|t| |η(t)| |θ(ζ)|`; the exceptional `ζ = λ/2π` is null.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory SchwartzMap FourierTransform
open scoped ENNReal

theorem ph_mul (a b t : ℝ) : ph a t * ph b t = ph (a + b) t := by
  simp only [ph, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fourierInv_schwartz_apply (f : 𝓢(ℝ, ℂ)) (y : ℝ) :
    (𝓕⁻ f : 𝓢(ℝ, ℂ)) y = ∫ t, ph (2 * Real.pi * y) t * f t := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ph, smul_eq_mul, RCLike.inner_apply, conj_trivial]
  ring_nf

theorem schwartz_eq_fourier (g : 𝓢(ℝ, ℂ)) (r : ℝ) :
    g r = ∫ ζ, ph (-(2 * Real.pi * ζ)) r * (𝓕⁻ g : 𝓢(ℝ, ℂ)) ζ := by
  have hs : g r = 𝓕 (⇑(𝓕⁻ g : 𝓢(ℝ, ℂ))) r := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  rw [hs, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [ph, smul_eq_mul, RCLike.inner_apply, conj_trivial]
  ring_nf

/-- The time integral `∫₀ᵗ e^{-iλ(t-r)} e^{-2πiζr} dr`. -/
def Mk (lam t ζ : ℝ) : ℂ := ∫ r in (0 : ℝ)..t, ph (-lam) (t - r) * ph (-(2 * Real.pi * ζ)) r

theorem continuous_Mk (lam : ℝ) : Continuous fun p : ℝ × ℝ => Mk lam p.1 p.2 := by
  have hf : Continuous fun q : (ℝ × ℝ) × ℝ =>
      ph (-lam) (q.1.1 - q.2) * ph (-(2 * Real.pi * q.1.2)) q.2 := by
    unfold ph
    fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0)
    (f := fun (p : ℝ × ℝ) (r : ℝ) => ph (-lam) (p.1 - r) * ph (-(2 * Real.pi * p.2)) r)
    hf continuous_fst

theorem norm_Mk_le (lam t ζ : ℝ) : ‖Mk lam t ζ‖ ≤ |t| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := 1)
    (f := fun r => ph (-lam) (t - r) * ph (-(2 * Real.pi * ζ)) r)
    (fun r _ => by simp [norm_ph])
  simpa [Mk] using h

theorem Mk_eq {lam ζ : ℝ} (hσ : 2 * Real.pi * ζ - lam ≠ 0) (t : ℝ) :
    Mk lam t ζ = (ph (-lam) t - ph (-(2 * Real.pi * ζ)) t) /
      (Complex.I * ((2 * Real.pi * ζ - lam : ℝ) : ℂ)) := by
  set c : ℂ := ((lam - 2 * Real.pi * ζ : ℝ) : ℂ) * Complex.I with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    refine mul_ne_zero ?_ Complex.I_ne_zero
    exact_mod_cast fun h : lam - 2 * Real.pi * ζ = 0 => hσ (by linarith)
  have e : ∀ r : ℝ, ph (-lam) (t - r) * ph (-(2 * Real.pi * ζ)) r =
      ph (-lam) t * Complex.exp (c * r) := fun r => by
    simp only [ph, hc, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : ph (-lam) t * Complex.exp (c * t) = ph (-(2 * Real.pi * ζ)) t := by
    simp only [ph, hc, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcI : Complex.I * ((2 * Real.pi * ζ - lam : ℝ) : ℂ) = -c := by
    rw [hc]
    push_cast
    ring
  unfold Mk
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc0, hcI]
  have e0 : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by simp
  rw [e0]
  calc ph (-lam) t * ((Complex.exp (c * t) - 1) / c)
      = (ph (-lam) t * Complex.exp (c * t) - ph (-lam) t) / c := by ring
    _ = (ph (-(2 * Real.pi * ζ)) t - ph (-lam) t) / c := by rw [e2]
    _ = (ph (-lam) t - ph (-(2 * Real.pi * ζ)) t) / -c := by rw [div_neg, ← neg_div, neg_sub]

/-- Fubini on `[0,t] × ℝ`: the Duhamel integral in terms of `θ = 𝓕⁻ g`. -/
theorem duhInt_eq (lam : ℝ) (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ∫ r in (0 : ℝ)..t, ph (-lam) (t - r) * g r =
      ∫ ζ, (𝓕⁻ g : 𝓢(ℝ, ℂ)) ζ * Mk lam t ζ := by
  have hθc := (𝓕⁻ g : 𝓢(ℝ, ℂ)).continuous
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top
      (measure_Icc_lt_top (μ := volume) (a := 0 ⊓ t) (b := 0 ⊔ t)).ne
      (measure_mono Set.Ioc_subset_Icc_self))
  have hc : Continuous fun p : ℝ × ℝ =>
      ph (-lam) (t - p.1) * (ph (-(2 * Real.pi * p.2)) p.1 * (𝓕⁻ g : 𝓢(ℝ, ℂ)) p.2) := by
    unfold ph
    fun_prop
  have hF : Integrable (Function.uncurry fun (r ζ : ℝ) =>
      ph (-lam) (t - r) * (ph (-(2 * Real.pi * ζ)) r * (𝓕⁻ g : 𝓢(ℝ, ℂ)) ζ))
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod volume) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod
      (𝓕⁻ g : 𝓢(ℝ, ℂ)).integrable.norm) hc.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by simp [Function.uncurry, norm_ph]
  calc ∫ r in (0 : ℝ)..t, ph (-lam) (t - r) * g r
      = ∫ r in (0 : ℝ)..t, ∫ ζ, ph (-lam) (t - r) *
          (ph (-(2 * Real.pi * ζ)) r * (𝓕⁻ g : 𝓢(ℝ, ℂ)) ζ) := by
        refine intervalIntegral.integral_congr fun r _ => ?_
        rw [schwartz_eq_fourier g r, ← integral_const_mul]
    _ = ∫ ζ, ∫ r in (0 : ℝ)..t, ph (-lam) (t - r) *
          (ph (-(2 * Real.pi * ζ)) r * (𝓕⁻ g : 𝓢(ℝ, ℂ)) ζ) :=
        intervalIntegral_integral_swap hF
    _ = ∫ ζ, (𝓕⁻ g : 𝓢(ℝ, ℂ)) ζ * Mk lam t ζ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
        simp only [Mk]
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun r _ => ?_
        ring

/-- Fubini on `ℝ × ℝ`: `𝓕⁻(duhOut)(ξ) = ∫ θ(ζ) ∫ e^{2πitξ} η(t) M(t,ζ) dt dζ`. -/
theorem fourierInv_duhOut (η : 𝓢(ℝ, ℂ)) (lam : ℝ) (g : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    (𝓕⁻ (duhOut η lam g) : 𝓢(ℝ, ℂ)) ξ =
      ∫ ζ, (𝓕⁻ g : 𝓢(ℝ, ℂ)) ζ * ∫ t, ph (2 * Real.pi * ξ) t * (η t * Mk lam t ζ) := by
  have hθc := (𝓕⁻ g : 𝓢(ℝ, ℂ)).continuous
  have hc : Continuous fun p : ℝ × ℝ =>
      ph (2 * Real.pi * ξ) p.1 * (η p.1 * ((𝓕⁻ g : 𝓢(ℝ, ℂ)) p.2 * Mk lam p.1 p.2)) :=
    ((continuous_ph _).comp continuous_fst).mul ((η.continuous.comp continuous_fst).mul
      ((hθc.comp continuous_snd).mul (continuous_Mk lam)))
  have hG : Integrable (Function.uncurry fun (t ζ : ℝ) =>
      ph (2 * Real.pi * ξ) t * (η t * ((𝓕⁻ g : 𝓢(ℝ, ℂ)) ζ * Mk lam t ζ))) (volume.prod volume) := by
    refine Integrable.mono' ((η.integrable_pow_mul volume 1).mul_prod
      (𝓕⁻ g : 𝓢(ℝ, ℂ)).integrable.norm) hc.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun p => ?_
    show ‖ph (2 * Real.pi * ξ) p.1 * (η p.1 * ((𝓕⁻ g : 𝓢(ℝ, ℂ)) p.2 * Mk lam p.1 p.2))‖ ≤
      ‖p.1‖ ^ 1 * ‖η p.1‖ * ‖(𝓕⁻ g : 𝓢(ℝ, ℂ)) p.2‖
    rw [norm_mul, norm_mul, norm_mul, norm_ph, one_mul]
    calc ‖η p.1‖ * (‖(𝓕⁻ g : 𝓢(ℝ, ℂ)) p.2‖ * ‖Mk lam p.1 p.2‖)
        ≤ ‖η p.1‖ * (‖(𝓕⁻ g : 𝓢(ℝ, ℂ)) p.2‖ * ‖p.1‖) := by
          gcongr
          rw [Real.norm_eq_abs]
          exact norm_Mk_le lam p.1 p.2
      _ = ‖p.1‖ ^ 1 * ‖η p.1‖ * ‖(𝓕⁻ g : 𝓢(ℝ, ℂ)) p.2‖ := by ring
  rw [fourierInv_schwartz_apply]
  calc ∫ t, ph (2 * Real.pi * ξ) t * duhOut η lam g t
      = ∫ t, ∫ ζ, ph (2 * Real.pi * ξ) t * (η t * ((𝓕⁻ g : 𝓢(ℝ, ℂ)) ζ * Mk lam t ζ)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        beta_reduce
        rw [duhOut_apply, duhInt_eq, ← integral_const_mul, ← integral_const_mul]
    _ = ∫ ζ, ∫ t, ph (2 * Real.pi * ξ) t * (η t * ((𝓕⁻ g : 𝓢(ℝ, ℂ)) ζ * Mk lam t ζ)) :=
        integral_integral_swap hG
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
        beta_reduce
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        ring

/-- Evaluation of the time integral: the fixed-cutoff Duhamel kernel. -/
theorem time_integral_eq_duhKer (η : 𝓢(ℝ, ℂ)) {lam ζ : ℝ} (ξ : ℝ)
    (hζ : ζ ≠ lam / (2 * Real.pi)) :
    ∫ t, ph (2 * Real.pi * ξ) t * (η t * Mk lam t ζ) =
      duhKer (𝓕⁻ η : 𝓢(ℝ, ℂ)) (ξ - lam / (2 * Real.pi)) (ζ - lam / (2 * Real.pi)) := by
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have ha : 2 * Real.pi * (lam / (2 * Real.pi)) = lam := by field_simp
  have hσ : 2 * Real.pi * ζ - lam ≠ 0 := by
    intro h
    apply hζ
    rw [eq_div_iff hπ]
    linarith
  have e1 : ∀ t, ph (2 * Real.pi * ξ) t * ph (-lam) t =
      ph (2 * Real.pi * (ξ - lam / (2 * Real.pi))) t := fun t => by
    rw [ph_mul, mul_sub, ha]
    ring_nf
  have e2 : ∀ t, ph (2 * Real.pi * ξ) t * ph (-(2 * Real.pi * ζ)) t =
      ph (2 * Real.pi * (ξ - lam / (2 * Real.pi) - (ζ - lam / (2 * Real.pi)))) t := fun t => by
    rw [ph_mul]
    ring_nf
  have hR : (ζ - lam / (2 * Real.pi)) * (2 * Real.pi) = 2 * Real.pi * ζ - lam := by
    rw [sub_mul, div_mul_cancel₀ lam hπ]
    ring
  have eD : (2 * (Real.pi : ℂ) * Complex.I * ((ζ - lam / (2 * Real.pi) : ℝ) : ℂ)) =
      Complex.I * ((2 * Real.pi * ζ - lam : ℝ) : ℂ) := by
    calc (2 * (Real.pi : ℂ) * Complex.I * ((ζ - lam / (2 * Real.pi) : ℝ) : ℂ))
        = Complex.I * (((ζ - lam / (2 * Real.pi)) * (2 * Real.pi) : ℝ) : ℂ) := by
          push_cast
          ring
      _ = Complex.I * ((2 * Real.pi * ζ - lam : ℝ) : ℂ) := by rw [hR]
  simp_rw [Mk_eq hσ]
  calc ∫ t, ph (2 * Real.pi * ξ) t * (η t * ((ph (-lam) t - ph (-(2 * Real.pi * ζ)) t) /
        (Complex.I * ((2 * Real.pi * ζ - lam : ℝ) : ℂ))))
      = ∫ t, (ph (2 * Real.pi * (ξ - lam / (2 * Real.pi))) t * η t -
          ph (2 * Real.pi * (ξ - lam / (2 * Real.pi) - (ζ - lam / (2 * Real.pi)))) t * η t) /
            (Complex.I * ((2 * Real.pi * ζ - lam : ℝ) : ℂ)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        beta_reduce
        rw [← e1 t, ← e2 t]
        ring
    _ = ((∫ t, ph (2 * Real.pi * (ξ - lam / (2 * Real.pi))) t * η t) -
          ∫ t, ph (2 * Real.pi * (ξ - lam / (2 * Real.pi) - (ζ - lam / (2 * Real.pi)))) t * η t) /
            (Complex.I * ((2 * Real.pi * ζ - lam : ℝ) : ℂ)) := by
        rw [integral_div, integral_sub (integrable_phg _ η) (integrable_phg _ η)]
    _ = _ := by
        unfold duhKer
        rw [fourierInv_schwartz_apply, fourierInv_schwartz_apply, eD]

/-- **Pointwise bound of the Duhamel output's inverse transform by the kernel.** -/
theorem enorm_fourierInv_duhOut_le (η : 𝓢(ℝ, ℂ)) (lam : ℝ) (g : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    ‖(𝓕⁻ (duhOut η lam g) : 𝓢(ℝ, ℂ)) ξ‖ₑ ≤
      ∫⁻ z, ‖duhKer (𝓕⁻ η : 𝓢(ℝ, ℂ)) (ξ - lam / (2 * Real.pi)) z‖ₑ *
        ‖(𝓕⁻ g : 𝓢(ℝ, ℂ)) (z + lam / (2 * Real.pi))‖ₑ := by
  have hae : ∀ᵐ ζ : ℝ, ζ ≠ lam / (2 * Real.pi) := by
    rw [ae_iff]
    simp
  have hcongr : (fun ζ => (𝓕⁻ g : 𝓢(ℝ, ℂ)) ζ * ∫ t, ph (2 * Real.pi * ξ) t * (η t * Mk lam t ζ))
      =ᵐ[volume] fun ζ => (𝓕⁻ g : 𝓢(ℝ, ℂ)) ζ *
        duhKer (𝓕⁻ η : 𝓢(ℝ, ℂ)) (ξ - lam / (2 * Real.pi)) (ζ - lam / (2 * Real.pi)) :=
    hae.mono fun ζ hζ => by
      beta_reduce
      rw [time_integral_eq_duhKer η ξ hζ]
  rw [fourierInv_duhOut, integral_congr_ae hcongr]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  rw [← lintegral_add_right_eq_self _ (lam / (2 * Real.pi))]
  congr 1
  funext z
  simp only [enorm_mul, add_sub_cancel_right]
  rw [mul_comm]

end LiebLiniger.FixedPeriod.ALLS.PdeB
