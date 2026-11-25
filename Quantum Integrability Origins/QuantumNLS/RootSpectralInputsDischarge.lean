import Mathlib
import QuantumNLS.Prop017Physical
import QuantumNLS.RootDensityIdentification
import QuantumNLS.RootTraceSymbolFinal
import QuantumNLS.RootTraceAsymptotics
import QuantumNLS.PhysicalUpperTraceIdentity
import QuantumNLS.FullMassLimit

/-!
# PROP-017: discharging `Prop017Physical.RootSpectralInputs` for the actual `μ_{κ,u}`, except the even moments

Source: `window_reconstruction.tex`, "Precise spectral hypotheses", hypothesis 1 (moments) and hypothesis 2 (high regular cuts);
`high_band_cuts.tex` (R-0E2470A5, R-B7FD5D45); `ROOT_spectral_density.tex` (R-7E0532E7); `positive_moments.tex` (R-275B7656).

Setting: `κ > 0`, `u` a unit vector with a continuous `L`-periodic representative `uf` (`BulkResponseActual.IsPeriodicRepresentative`; the source takes `u` smooth),
and `μ` the limiting rapidity measure (`IsLimitingRapidityMeasure`).  For every height `h > 0` we PROVE the two geometric fields of `RootSpectralInputs`
(`rootSpectralInputs_geometry`):

* `gap`: with `δ = 1/L` and `ℓ₀` large, for every `ℓ ≥ ℓ₀` a.e. `x` for `μ` has `δ ≤ |x ∓ a_ℓ|`, `a_ℓ = (2ℓ+1)π/L`.
  (Density identification `RootDensityIdentification.root_density` and the real trace asymptotic `Δ(t) - 2cos(tL/2) → 0`: on `|t ∓ a_ℓ| < 1/L`, `|t|` large,
  `|Δ(t)| < 3/2 < 2`, so the density `(πκ)⁻¹ hfun |Δ|` vanishes there.)
* `discr`: `|D| ≥ d₀` on `Γ_ℓ` (`ℓ ≥ ℓ₀`) with explicit `d₀ = dlow L κ δ h > 0`.
  (`D = -2i e^{iLz/2} sin γ`, `γ = Lz/2 - κG`.  On the horizontal pieces and away from the real axis `|sin γ| ≥ sinh(L|Im z|/2)` since `Im γ = Im z (L/2 + κ ∫ |z-q|⁻²)`;
  near a cut `c = ±a_ℓ`, the gap makes `|G(c+iy) - G(c)| ≤ |y|/δ²`, `γ(c)` is real, `2cos γ(c) = Δ(c)` by the upper-half-plane cosine identity and continuity,
  `|Δ(c)| ≤ 1/2`, hence `|sin γ(c)| ≥ 3/4` and `|sin Re γ(c+iy)| ≥ 1/2` for `|y|(L/2 + κ/δ²) ≤ 1/4`.)
Only continuity of `u` is used for these two fields.

The third field (all even moments of `μ`) is NOT derived here.  It does NOT follow from `μ = ρ dt` with `ρ ≤ C` (a bounded density has no
moment decay); in the printed source it is R-275B7656 (`positive_moments.tex`, `moments:thm:moments`), proved for SMOOTH `u` by a formal expansion of the
Cauchy transform at infinity.  It is kept as the explicit named hypothesis `EvenMoments μ`; `rootSpectralInputs` assembles `RootSpectralInputs` from it.
No EXT-025 contract is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped Real ENNReal

noncomputable section

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace QuantumNLS.RootSpectralInputsDischarge

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.PhysicalQuantumMeasure (measure)
open QuantumNLS.SpatialTransfer (boundaryPhase)
open QuantumNLS.EmpiricalRapidity (cauchyTransform)
open QuantumNLS.Extrapolation (Gfull)
open QuantumNLS.NonvanishingD (Dsrc)
open QuantumNLS.ResolventNeighborhood (GammaN)
open QuantumNLS.PROP017UniformN (cutSeq)
open QuantumNLS.BulkResponseActual (IsLimitingRapidityMeasure IsPeriodicRepresentative)
open QuantumNLS.Prop017Physical (RootSpectralInputs)

/-- The even-moment input (R-275B7656 for smooth `u`), kept as an explicit named hypothesis. -/
def EvenMoments (μ : Measure ℝ) : Prop := ∀ p : ℕ, Integrable (fun x : ℝ => x ^ (2 * p)) μ

/-! ## 1. Elementary complex facts (no hypotheses on `u`) -/

section Elementary

variable {L κ : ℝ}

theorem Gfull_eq (μ : Measure ℝ) (z : ℂ) : Gfull μ z = cauchyTransform μ z := by
  unfold Gfull cauchyTransform
  simp [one_div]

theorem norm_sin_sq (w : ℂ) : ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sin_eq]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sin_ofReal_re,
    Complex.sin_ofReal_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.cosh_ofReal_re,
    Complex.cosh_ofReal_im, Complex.sinh_ofReal_re, Complex.sinh_ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, sub_zero, add_zero, mul_one, zero_sub, neg_mul, mul_neg, neg_neg]
  linear_combination Real.sin w.re ^ 2 * Real.cosh_sq w.im +
    Real.sinh w.im ^ 2 * Real.sin_sq_add_cos_sq w.re - 0

theorem im_phase' (μ : Measure ℝ) (z : ℂ) :
    (boundaryPhase L κ μ z).im = L * z.im / 2 - κ * (cauchyTransform μ z).im := by
  unfold boundaryPhase
  simp [Complex.mul_im, Complex.sub_im]
  try ring

/-- `D = -2i e^{iLz/2} sin γ`. -/
theorem Dsrc_eq (μ : Measure ℝ) (z : ℂ) :
    Dsrc κ L μ z = (-2 * Complex.I * Complex.exp (Complex.I * L * z / 2)) * Complex.sin (boundaryPhase L κ μ z) := by
  unfold Dsrc
  rw [Gfull_eq]
  set G := cauchyTransform μ z with hG
  set γ := boundaryPhase L κ μ z with hγ
  have hγ' : γ = (L : ℂ) * z / 2 - (κ : ℂ) * G := rfl
  have h1 : Complex.exp (Complex.I * L * z / 2) * Complex.exp (-γ * Complex.I) =
      Complex.exp (Complex.I * κ * G) := by
    rw [← Complex.exp_add]; congr 1; rw [hγ']; ring
  have h2 : Complex.exp (Complex.I * L * z / 2) * Complex.exp (γ * Complex.I) =
      Complex.exp (Complex.I * L * z) / Complex.exp (Complex.I * κ * G) := by
    rw [← Complex.exp_add, ← Complex.exp_sub]; congr 1; rw [hγ']; ring
  rw [Complex.sin]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have key : (-2 * Complex.I * Complex.exp (Complex.I * L * z / 2)) *
      ((Complex.exp (-γ * Complex.I) - Complex.exp (γ * Complex.I)) * Complex.I / 2) =
      Complex.exp (Complex.I * L * z / 2) * Complex.exp (-γ * Complex.I) -
        Complex.exp (Complex.I * L * z / 2) * Complex.exp (γ * Complex.I) := by
    linear_combination (-(Complex.exp (Complex.I * L * z / 2) * (Complex.exp (-γ * Complex.I) -
      Complex.exp (γ * Complex.I)))) * hI
  rw [key, h1, h2]

theorem norm_Dsrc (μ : Measure ℝ) (z : ℂ) :
    ‖Dsrc κ L μ z‖ = 2 * Real.exp (-(L * z.im) / 2) * ‖Complex.sin (boundaryPhase L κ μ z)‖ := by
  rw [Dsrc_eq, norm_mul, norm_mul, norm_mul, Complex.norm_exp]
  have : (Complex.I * (L : ℂ) * z / 2).re = -(L * z.im) / 2 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  simp [Complex.norm_I]

end Elementary

/-! ## 2. The imaginary part of the phase and the `sinh` bound -/

section ImPhase

variable {L κ : ℝ}

/-- `|Im γ(z)| ≥ L|Im z|/2` off the real axis. -/
theorem im_phase_ge (μ : Measure ℝ) [IsFiniteMeasure μ] (hκ : 0 < κ) (hL : 0 ≤ L) {z : ℂ} (hz : z.im ≠ 0) :
    L * |z.im| / 2 ≤ |(boundaryPhase L κ μ z).im| := by
  have hint := QuantumNLS.EmpiricalRapidity.integrable_cauchyIntegrand μ z hz
  have hneg : z.im * (cauchyTransform μ z).im ≤ 0 := by
    have him : (cauchyTransform μ z).im = ∫ q : ℝ, (((z - (q : ℂ))⁻¹).im) ∂μ := by
      unfold cauchyTransform
      have := Complex.imCLM.integral_comp_comm hint
      simp only [Complex.imCLM_apply] at this
      exact this.symm
    rw [him, ← integral_const_mul]
    refine integral_nonpos fun q => ?_
    simp only [Pi.zero_apply]
    rw [Complex.inv_im]
    have : (z - (q : ℂ)).im = z.im := by simp
    rw [this]
    have hns : 0 ≤ Complex.normSq (z - (q : ℂ)) := Complex.normSq_nonneg _
    have : z.im * (-z.im / Complex.normSq (z - (q : ℂ))) = -(z.im ^ 2 / Complex.normSq (z - (q : ℂ))) := by
      ring
    rw [this]
    have : 0 ≤ z.im ^ 2 / Complex.normSq (z - (q : ℂ)) := div_nonneg (sq_nonneg _) hns
    linarith
  have hy : 0 < |z.im| := abs_pos.2 hz
  have h1 : L * z.im ^ 2 / 2 ≤ z.im * (boundaryPhase L κ μ z).im := by
    rw [im_phase']
    nlinarith [hneg, hκ]
  by_contra hlt
  push Not at hlt
  have h2 : |z.im| * |(boundaryPhase L κ μ z).im| < |z.im| * (L * |z.im| / 2) :=
    mul_lt_mul_of_pos_left hlt hy
  have h3 : z.im * (boundaryPhase L κ μ z).im ≤ |z.im| * |(boundaryPhase L κ μ z).im| := by
    rw [← abs_mul]; exact le_abs_self _
  have h4 : z.im ^ 2 = |z.im| ^ 2 := (sq_abs _).symm
  nlinarith [h1, h2, h3, h4]

theorem sinh_le_norm_sin {w : ℂ} {b : ℝ} (hb : 0 ≤ b) (hw : b ≤ |w.im|) :
    Real.sinh b ≤ ‖Complex.sin w‖ := by
  have hb0 : 0 ≤ Real.sinh b := Real.sinh_nonneg_iff.2 hb
  have hsq : Real.sinh b ^ 2 ≤ ‖Complex.sin w‖ ^ 2 := by
    rw [norm_sin_sq]
    have hmono : Real.sinh b ≤ |Real.sinh w.im| := by
      rcases le_total 0 w.im with h | h
      · rw [abs_of_nonneg h] at hw
        have := Real.sinh_le_sinh.2 hw
        exact le_trans this (le_abs_self _)
      · rw [abs_of_nonpos h] at hw
        have := Real.sinh_le_sinh.2 hw
        rw [Real.sinh_neg] at this
        exact le_trans this (neg_le_abs _)
    have : Real.sinh b ^ 2 ≤ |Real.sinh w.im| ^ 2 := pow_le_pow_left₀ hb0 hmono 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (Real.sin w.re)]
  exact (pow_le_pow_iff_left₀ hb0 (norm_nonneg _) two_ne_zero).1 hsq

end ImPhase


/-! ## 3. Near a cut with a gap -/

section Cut

variable {L κ : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem norm_ge_of_gap {δ c q : ℝ} {z : ℂ} (hz : z.re = c) (h : δ ≤ |q - c|) : δ ≤ ‖z - (q : ℂ)‖ := by
  have h2 := Complex.abs_re_le_norm (z - (q : ℂ))
  have h3 : (z - (q : ℂ)).re = c - q := by simp [hz]
  rw [h3] at h2
  rw [abs_sub_comm] at h
  linarith

theorem integrable_inv_gap {δ c : ℝ} (hδ : 0 < δ) (hg : ∀ᵐ q ∂μ, δ ≤ |q - c|) {z : ℂ} (hz : z.re = c) :
    Integrable (fun q : ℝ => (z - (q : ℂ))⁻¹) μ := by
  refine Integrable.mono' (integrable_const (δ⁻¹)) ?_ ?_
  · exact (measurable_const.sub Complex.measurable_ofReal).inv.aestronglyMeasurable
  · filter_upwards [hg] with q hq
    rw [norm_inv]
    exact inv_anti₀ hδ (norm_ge_of_gap hz hq)

theorem cauchy_lip {δ c : ℝ} (hδ : 0 < δ) (hg : ∀ᵐ q ∂μ, δ ≤ |q - c|) (y : ℝ) :
    ‖cauchyTransform μ ((c : ℂ) + (y : ℂ) * Complex.I) - cauchyTransform μ (c : ℂ)‖ ≤ |y| / δ ^ 2 := by
  have hz : ((c : ℂ) + (y : ℂ) * Complex.I).re = c := by simp
  have hz0 : ((c : ℂ)).re = c := by simp
  unfold cauchyTransform
  rw [← integral_sub (integrable_inv_gap hδ hg hz) (integrable_inv_gap hδ hg hz0)]
  have hb : ∀ᵐ (q : ℝ) ∂μ, ‖((c : ℂ) + (y : ℂ) * Complex.I - (q : ℂ))⁻¹ - ((c : ℂ) - (q : ℂ))⁻¹‖ ≤ |y| / δ ^ 2 := by
    filter_upwards [hg] with q hq
    have h1 := norm_ge_of_gap hz hq
    have h2 := norm_ge_of_gap hz0 hq
    have hb0 : ((c : ℂ) + (y : ℂ) * Complex.I - (q : ℂ)) ≠ 0 := by
      intro h; rw [h, norm_zero] at h1; linarith
    have ha0 : ((c : ℂ) - (q : ℂ)) ≠ 0 := by
      intro h; rw [h, norm_zero] at h2; linarith
    rw [inv_sub_inv hb0 ha0, norm_div, norm_mul]
    have hnum : ‖((c : ℂ) - (q : ℂ)) - ((c : ℂ) + (y : ℂ) * Complex.I - (q : ℂ))‖ = |y| := by
      have : ((c : ℂ) - (q : ℂ)) - ((c : ℂ) + (y : ℂ) * Complex.I - (q : ℂ)) = -((y : ℂ) * Complex.I) := by ring
      rw [this, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [hnum]
    have hd : δ ^ 2 ≤ ‖(c : ℂ) + (y : ℂ) * Complex.I - (q : ℂ)‖ * ‖(c : ℂ) - (q : ℂ)‖ := by
      rw [sq]; exact mul_le_mul h1 h2 hδ.le (norm_nonneg _)
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hd
  calc _ ≤ |y| / δ ^ 2 * μ.real (univ : Set ℝ) := norm_integral_le_of_norm_le_const hb
    _ = |y| / δ ^ 2 := by simp

theorem im_cauchy_cut {δ c : ℝ} (hδ : 0 < δ) (hg : ∀ᵐ q ∂μ, δ ≤ |q - c|) :
    (cauchyTransform μ (c : ℂ)).im = 0 := by
  have hint := integrable_inv_gap hδ hg (z := (c : ℂ)) (by simp)
  unfold cauchyTransform
  have := Complex.imCLM.integral_comp_comm hint
  simp only [Complex.imCLM_apply] at this
  rw [← this]
  have h0 : ∀ q : ℝ, (((c : ℂ) - (q : ℂ))⁻¹).im = 0 := fun q => by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_inv]; exact Complex.ofReal_im _
  simp [h0]

theorem phase_lip (hκ : 0 < κ) (hL : 0 ≤ L) {δ c : ℝ} (hδ : 0 < δ) (hg : ∀ᵐ q ∂μ, δ ≤ |q - c|) (y : ℝ) :
    ‖boundaryPhase L κ μ ((c : ℂ) + (y : ℂ) * Complex.I) - boundaryPhase L κ μ (c : ℂ)‖ ≤
      |y| * (L / 2 + κ / δ ^ 2) := by
  have e : boundaryPhase L κ μ ((c : ℂ) + (y : ℂ) * Complex.I) - boundaryPhase L κ μ (c : ℂ) =
      (L : ℂ) * ((y : ℂ) * Complex.I) / 2 -
        (κ : ℂ) * (cauchyTransform μ ((c : ℂ) + (y : ℂ) * Complex.I) - cauchyTransform μ (c : ℂ)) := by
    unfold boundaryPhase; ring
  rw [e]
  have h1 : ‖(L : ℂ) * ((y : ℂ) * Complex.I) / 2‖ = L * |y| / 2 := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL]
    simp
  have h2 : ‖(κ : ℂ) * (cauchyTransform μ ((c : ℂ) + (y : ℂ) * Complex.I) - cauchyTransform μ (c : ℂ))‖ ≤
      κ * (|y| / δ ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
    exact mul_le_mul_of_nonneg_left (cauchy_lip hδ hg y) hκ.le
  calc _ ≤ ‖(L : ℂ) * ((y : ℂ) * Complex.I) / 2‖ + ‖(κ : ℂ) * (cauchyTransform μ ((c : ℂ) + (y : ℂ) * Complex.I) -
          cauchyTransform μ (c : ℂ))‖ := norm_sub_le _ _
    _ ≤ L * |y| / 2 + κ * (|y| / δ ^ 2) := by rw [h1]; linarith
    _ = |y| * (L / 2 + κ / δ ^ 2) := by ring

/-- **Lower bound for `|sin γ|` near a gapped cut.**  If the support of `μ` has distance `≥ δ` from `c`, `2 cos γ = Δ` on the upper half-plane for a continuous `Δ`,
and `‖Δ(c)‖ ≤ 1/2`, then `|sin γ(c+iy)| ≥ 1/2` for `|y| (L/2 + κ/δ²) ≤ 1/4`. -/
theorem sin_lower_cut (hκ : 0 < κ) (hL : 0 ≤ L) {δ c : ℝ} (hδ : 0 < δ) (hg : ∀ᵐ q ∂μ, δ ≤ |q - c|)
    {Δ : ℂ → ℂ} (hΔ : Continuous Δ)
    (hcos : ∀ z : ℂ, 0 < z.im → 2 * Complex.cos (boundaryPhase L κ μ z) = Δ z)
    (hΔc : ‖Δ (c : ℂ)‖ ≤ 1 / 2) {y : ℝ} (hy : |y| * (L / 2 + κ / δ ^ 2) ≤ 1 / 4) :
    1 / 2 ≤ ‖Complex.sin (boundaryPhase L κ μ ((c : ℂ) + (y : ℂ) * Complex.I))‖ := by
  set g := boundaryPhase L κ μ (c : ℂ) with hg_def
  have hgim : g.im = 0 := by
    rw [hg_def, im_phase', im_cauchy_cut hδ hg]; simp
  have hlim1 : Tendsto (fun t : ℝ => boundaryPhase L κ μ ((c : ℂ) + (t : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 g) := by
    have hC : Tendsto (fun t : ℝ => |t| * (L / 2 + κ / δ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => |t| * (L / 2 + κ / δ ^ 2)) (𝓝 0) (𝓝 (|(0 : ℝ)| * (L / 2 + κ / δ ^ 2))) :=
        (continuous_abs.mul continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    exact tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero (fun _ => norm_nonneg _) (fun t => phase_lip hκ hL hδ hg t) hC)
  have hlim2 : Tendsto (fun t : ℝ => 2 * Complex.cos (boundaryPhase L κ μ ((c : ℂ) + (t : ℂ) * Complex.I)))
      (𝓝[>] 0) (𝓝 (2 * Complex.cos g)) :=
    ((continuous_const.mul Complex.continuous_cos).continuousAt.tendsto).comp hlim1
  have hlim3 : Tendsto (fun t : ℝ => Δ ((c : ℂ) + (t : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 (Δ (c : ℂ))) := by
    have hc : Continuous fun t : ℝ => ((c : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    have := (hΔ.comp hc).tendsto 0
    simpa [Function.comp_def] using this.mono_left nhdsWithin_le_nhds
  have hcg : 2 * Complex.cos g = Δ (c : ℂ) :=
    tendsto_nhds_unique_of_eventuallyEq hlim2 hlim3 (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hcos _ (by simpa using ht))
  have hnorm : ‖Complex.cos g‖ ≤ 1 / 4 := by
    have : ‖Complex.cos g‖ = ‖Δ (c : ℂ)‖ / 2 := by
      rw [← hcg, norm_mul]; simp
    linarith
  have hgre : g = (g.re : ℂ) := Complex.ext (by simp) (by simp [hgim])
  have hcosθ : |Real.cos g.re| ≤ 1 / 4 := by
    have : Complex.cos g = ((Real.cos g.re : ℝ) : ℂ) := by
      conv_lhs => rw [hgre]
      exact (Complex.ofReal_cos _).symm
    rw [this, Complex.norm_real, Real.norm_eq_abs] at hnorm
    exact hnorm
  have hsinθ : 3 / 4 ≤ |Real.sin g.re| := by
    by_contra hlt
    push Not at hlt
    have h1 := Real.sin_sq_add_cos_sq g.re
    have h2 : Real.cos g.re ^ 2 ≤ 1 / 16 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hcosθ 2
      rw [sq_abs] at this
      linarith
    have h3 : Real.sin g.re ^ 2 < 9 / 16 := by
      have := pow_lt_pow_left₀ hlt (abs_nonneg _) (two_ne_zero)
      rw [sq_abs] at this
      linarith
    linarith
  set z : ℂ := (c : ℂ) + (y : ℂ) * Complex.I with hz
  have hre : |(boundaryPhase L κ μ z).re - g.re| ≤ 1 / 4 := by
    have h1 := Complex.abs_re_le_norm (boundaryPhase L κ μ z - g)
    have h2 : (boundaryPhase L κ μ z - g).re = (boundaryPhase L κ μ z).re - g.re := by simp
    rw [h2] at h1
    exact le_trans h1 (le_trans (phase_lip hκ hL hδ hg y) hy)
  have hsx : 1 / 2 ≤ |Real.sin (boundaryPhase L κ μ z).re| := by
    have h1 := Real.abs_sin_sub_sin_le (boundaryPhase L κ μ z).re g.re
    have h5 := abs_sub_abs_le_abs_sub (Real.sin g.re) (Real.sin (boundaryPhase L κ μ z).re)
    rw [abs_sub_comm] at h5
    linarith
  have hsq : (1 / 2 : ℝ) ^ 2 ≤ ‖Complex.sin (boundaryPhase L κ μ z)‖ ^ 2 := by
    rw [norm_sin_sq]
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hsx 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (Real.sinh (boundaryPhase L κ μ z).im)]
  exact (pow_le_pow_iff_left₀ (by norm_num) (norm_nonneg _) two_ne_zero).1 hsq

end Cut

/-! ## 4. The lower bound on `Γ` -/

section Gamma

variable {L κ : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]

def yzero (L κ δ : ℝ) : ℝ := 1 / (4 * (L / 2 + κ / δ ^ 2))

def slow (L κ δ h : ℝ) : ℝ := min (1 / 2) (min (Real.sinh (L * yzero L κ δ / 2)) (Real.sinh (L * h / 2)))

/-- The explicit lower bound `d₀`. -/
def dlow (L κ δ h : ℝ) : ℝ := 2 * Real.exp (-(L * h) / 2) * slow L κ δ h

theorem dlow_pos (hκ : 0 < κ) (hL : 0 < L) {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h) : 0 < dlow L κ δ h := by
  have hy0 : 0 < yzero L κ δ := by unfold yzero; positivity
  have : 0 < slow L κ δ h := by
    unfold slow
    refine lt_min (by norm_num) (lt_min ?_ ?_)
    · exact Real.sinh_pos_iff.2 (by positivity)
    · exact Real.sinh_pos_iff.2 (by positivity)
  unfold dlow
  positivity

theorem norm_Dsrc_lower (hκ : 0 < κ) (hL : 0 < L) {δ a h : ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (hga : ∀ᵐ q ∂μ, δ ≤ |q - a|) (hgb : ∀ᵐ q ∂μ, δ ≤ |q - (-a)|)
    {Δ : ℂ → ℂ} (hΔ : Continuous Δ)
    (hcos : ∀ z : ℂ, 0 < z.im → 2 * Complex.cos (boundaryPhase L κ μ z) = Δ z)
    (hΔa : ‖Δ (a : ℂ)‖ ≤ 1 / 2) (hΔb : ‖Δ ((-a : ℝ) : ℂ)‖ ≤ 1 / 2)
    {w : ℂ} (hw : w ∈ GammaN a h) : dlow L κ δ h ≤ ‖Dsrc κ L μ w‖ := by
  have hCc : 0 < L / 2 + κ / δ ^ 2 := by positivity
  have hy0 : 0 < yzero L κ δ := by unfold yzero; positivity
  have near : ∀ c : ℝ, (∀ᵐ q ∂μ, δ ≤ |q - c|) → ‖Δ (c : ℂ)‖ ≤ 1 / 2 → w.re = c →
      |w.im| * (L / 2 + κ / δ ^ 2) ≤ 1 / 4 →
      1 / 2 ≤ ‖Complex.sin (boundaryPhase L κ μ w)‖ := by
    intro c hg hΔc hre hy
    have hwe : w = (c : ℂ) + (w.im : ℂ) * Complex.I := Complex.ext (by simp [hre]) (by simp)
    have := sin_lower_cut hκ hL.le hδ hg hΔ hcos hΔc hy
    rwa [← hwe] at this
  have far : yzero L κ δ < |w.im| → slow L κ δ h ≤ ‖Complex.sin (boundaryPhase L κ μ w)‖ := by
    intro hyz
    have hne : w.im ≠ 0 := by
      intro h0; rw [h0, abs_zero] at hyz; linarith
    have h1 := im_phase_ge μ hκ hL.le hne
    refine le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) ?_
    refine sinh_le_norm_sin (by positivity) (le_trans ?_ h1)
    nlinarith
  have hs : slow L κ δ h ≤ ‖Complex.sin (boundaryPhase L κ μ w)‖ ∧ |w.im| ≤ h := by
    simp only [GammaN, Set.mem_union, Set.mem_setOf_eq] at hw
    rcases hw with ⟨hre, him⟩ | ⟨him, hre⟩
    · refine ⟨?_, him⟩
      by_cases hn : |w.im| * (L / 2 + κ / δ ^ 2) ≤ 1 / 4
      · refine le_trans (min_le_left _ _) ?_
        rcases hre with hre | hre
        · exact near a hga hΔa hre hn
        · exact near (-a) hgb hΔb hre hn
      · apply far
        push Not at hn
        unfold yzero
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
    · have habs : |w.im| = h := by
        rcases him with him | him
        · rw [him, abs_of_pos hh]
        · rw [him, abs_neg, abs_of_pos hh]
      have hne : w.im ≠ 0 := by
        intro h0; rw [h0, abs_zero] at habs; linarith
      have h1 := im_phase_ge μ hκ hL.le hne
      refine ⟨?_, habs.le⟩
      refine le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) ?_
      refine sinh_le_norm_sin (by positivity) (le_trans ?_ h1)
      rw [habs]
  obtain ⟨hs1, hs2⟩ := hs
  rw [norm_Dsrc]
  unfold dlow
  have he : Real.exp (-(L * h) / 2) ≤ Real.exp (-(L * w.im) / 2) := by
    apply Real.exp_le_exp.2
    have : w.im ≤ h := le_trans (le_abs_self _) hs2
    nlinarith
  have hs0 : 0 ≤ slow L κ δ h := by
    unfold slow
    refine le_min (by norm_num) (le_min ?_ ?_)
    · exact Real.sinh_nonneg_iff.2 (by positivity)
    · exact Real.sinh_nonneg_iff.2 (by positivity)
  exact mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) hs1 hs0 (by positivity)

end Gamma

/-! ## 5. The actual measure: gap and discriminant bound -/

section Actual

variable {L κ : ℝ} [Fact (0 < L)]

open QuantumNLS.RootDiscriminant (discReal)
open QuantumNLS.RootDensityIdentification (dens disc_eq_rep)

/-- The limiting rapidity measure of a unit `u` is the canonical full-mass measure. -/
theorem measure_eq_limit (hκ : 0 < κ) {u : L2T L} (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) : (μ : Measure ℝ) = measure hκ u := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
  have h1 : μ = QuantumNLS.FreeLimit.muKappa u hu κ :=
    hμ.unique (QuantumNLS.FreeLimit.muKappa_spec u hu hκ)
  rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas, QuantumNLS.FullMass.Mmeas_of_ne κ hu0, h1]
  have hdir : QuantumNLS.FullMass.unitDir u = u := by
    unfold QuantumNLS.FullMass.unitDir
    rw [hu]; simp
  have hk : κ * ‖u‖ ^ 2 = κ := by rw [hu]; ring
  rw [hk, QuantumNLS.FullMassLimit.muKappa_congr hdir (QuantumNLS.FullMass.norm_unitDir hu0) hu κ, hu]
  simp

/-- `cos` at a cut point and the Lipschitz-in-`s` bound. -/
theorem cos_cut_bound {a : ℝ} (hLpos : 0 < L) (l : ℕ) (ha : a = cutSeq L l ∨ a = -cutSeq L l) (s : ℝ) :
    Real.cos (a * L / 2) = 0 ∧ |Real.cos ((a + s) * L / 2)| ≤ |s| * L / 2 := by
  have hc : cutSeq L l * L / 2 = (2 * (l : ℝ) + 1) * Real.pi / 2 := by
    unfold cutSeq; field_simp
  have hcos0 : Real.cos (a * L / 2) = 0 := by
    rcases ha with ha | ha
    · rw [ha, hc]
      exact Real.cos_eq_zero_iff.2 ⟨(l : ℤ), by push_cast; ring⟩
    · have : -cutSeq L l * L / 2 = -(cutSeq L l * L / 2) := by ring
      rw [ha, this, Real.cos_neg, hc]
      exact Real.cos_eq_zero_iff.2 ⟨(l : ℤ), by push_cast; ring⟩
  refine ⟨hcos0, ?_⟩
  have e : (a + s) * L / 2 = a * L / 2 + s * L / 2 := by ring
  rw [e, Real.cos_add, hcos0, zero_mul, zero_sub, abs_neg, abs_mul]
  have h1 : |Real.sin (a * L / 2)| ≤ 1 := Real.abs_sin_le_one _
  have h2 : |Real.sin (s * L / 2)| ≤ |s * L / 2| := Real.abs_sin_le_abs
  have h3 : |s * L / 2| = |s| * L / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hLpos]; norm_num
  rw [h3] at h2
  calc _ ≤ 1 * (|s| * L / 2) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- Smallness of the real discriminant near the cuts for `ℓ` large (trace asymptotic). -/
theorem disc_small (hκ : 0 < κ) {uf : ℝ → ℂ} (hcont : Continuous uf) :
    ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ a : ℝ, (a = cutSeq L l ∨ a = -cutSeq L l) →
      (∀ s : ℝ, |s| < 1 / L → |discReal L κ uf (a + s)| < 3 / 2) ∧ |discReal L κ uf a| ≤ 1 / 2 := by
  have hL : 0 < L := Fact.out
  have h1 := (Metric.tendsto_nhds.1
    (QuantumNLS.RootTraceAsymptotics.trace_asymptotic hκ hcont hL.le)) (1 / 2) (by norm_num)
  rw [cocompact_eq_atBot_atTop, Filter.eventually_sup, Filter.eventually_atBot, Filter.eventually_atTop] at h1
  obtain ⟨⟨T2, hT2⟩, ⟨T1, hT1⟩⟩ := h1
  have hT : ∀ t : ℝ, max T1 (-T2) ≤ |t| → |discReal L κ uf t - 2 * Real.cos (t * L / 2)| < 1 / 2 := by
    intro t ht
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h] at ht
      have := hT1 t (le_trans (le_max_left _ _) ht)
      simpa [Real.dist_eq] using this
    · rw [abs_of_nonpos h] at ht
      have : t ≤ T2 := by have := le_trans (le_max_right _ _) ht; linarith
      have := hT2 t this
      simpa [Real.dist_eq] using this
  obtain ⟨l0, hl0⟩ := exists_nat_gt ((max T1 (-T2) + 1 / L) * L)
  refine ⟨l0, fun l hl a ha => ?_⟩
  have hapos : max T1 (-T2) + 1 / L < |a| := by
    have habs : |a| = cutSeq L l := by
      rcases ha with ha | ha
      · rw [ha]; unfold cutSeq; exact abs_of_nonneg (by positivity)
      · rw [ha, abs_neg]; unfold cutSeq; exact abs_of_nonneg (by positivity)
    rw [habs]
    unfold cutSeq
    rw [lt_div_iff₀ hL]
    have hlle : (l0 : ℝ) ≤ l := by exact_mod_cast hl
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hl0' : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith
  have key : ∀ s : ℝ, |s| < 1 / L → |discReal L κ uf (a + s)| < 3 / 2 := by
    intro s hs
    have hsL : |s| * L < 1 := by
      have := (lt_div_iff₀ hL).1 hs
      exact this
    have habs : max T1 (-T2) ≤ |a + s| := by
      have := abs_sub_abs_le_abs_sub a (a + s)
      rw [show a - (a + s) = -s by ring, abs_neg] at this
      linarith
    have hd := hT (a + s) habs
    obtain ⟨-, hc⟩ := cos_cut_bound hL l ha s
    have hc2 : |2 * Real.cos ((a + s) * L / 2)| ≤ |s| * L := by
      rw [abs_mul]; norm_num; linarith
    have := abs_sub_abs_le_abs_sub (discReal L κ uf (a + s)) (2 * Real.cos ((a + s) * L / 2))
    linarith
  refine ⟨key, ?_⟩
  have hd := hT (a + 0) (by
    rw [add_zero]
    exact le_of_lt (lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hapos))
  obtain ⟨hc0, -⟩ := cos_cut_bound hL l ha 0
  rw [add_zero, hc0] at hd
  simp at hd
  linarith [hd]

/-- Density vanishes near cuts where the real discriminant is small: `μ` has a gap. -/
theorem gap_ae (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {uf : ℝ → ℂ} (hrep : IsPeriodicRepresentative L u uf)
    {c : ℝ} (hs : ∀ s : ℝ, |s| < 1 / L → |discReal L κ uf (c + s)| < 3 / 2) :
    ∀ᵐ q ∂(measure hκ u), 1 / L ≤ |q - c| := by
  have hL : 0 < L := Fact.out
  have hS : measure hκ u (Set.Ioo (c - 1 / L) (c + 1 / L)) = 0 := by
    rw [QuantumNLS.RootDensityIdentification.root_density hκ hu, withDensity_apply _ measurableSet_Ioo]
    rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => 0) ?_]
    · simp
    intro x hx
    have hxs : |x - c| < 1 / L := by
      rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
    have hx3 := hs (x - c) hxs
    rw [show c + (x - c) = x by ring] at hx3
    have hd : dens κ u x = 0 := by
      unfold dens
      rw [disc_eq_rep hrep κ (x : ℂ)]
      have : QuantumNLS.RootDensity.hfun |(QuantumNLS.SpatialTransfer.discriminant L κ uf (x : ℂ)).re| = 0 := by
        unfold QuantumNLS.RootDensity.hfun
        rw [if_neg]
        change ¬ (2 < |discReal L κ uf x|)
        linarith
      rw [this, mul_zero]
    simp [hd]
  have := measure_eq_zero_iff_ae_notMem.1 hS
  filter_upwards [this] with q hq
  by_contra hlt
  push Not at hlt
  apply hq
  rw [abs_lt] at hlt
  exact ⟨by linarith [hlt.1], by linarith [hlt.2]⟩

/-- The two geometric fields of `RootSpectralInputs` for the actual measure (`δ = 1/L`, `d₀ = dlow L κ (1/L) h`). -/
theorem rootSpectralInputs_geometry (hκ : 0 < κ) {u : L2T L} (hu : ‖u‖ = 1) {uf : ℝ → ℂ}
    (hrep : IsPeriodicRepresentative L u uf) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h : ℝ} (hh : 0 < h) :
    ∃ l0 : ℕ,
      (∀ l : ℕ, l0 ≤ l → ∀ᵐ x ∂(μ : Measure ℝ), 1 / L ≤ |x - cutSeq L l| ∧ 1 / L ≤ |x + cutSeq L l|) ∧
      (∀ l : ℕ, l0 ≤ l → ∀ w ∈ GammaN (cutSeq L l) h,
        dlow L κ (1 / L) h ≤ ‖Dsrc κ L (μ : Measure ℝ) w‖) := by
  have hL : 0 < L := Fact.out
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hu; exact zero_ne_one hu
  have hmeas := measure_eq_limit hκ hu hμ
  obtain ⟨l0, hl0⟩ := disc_small (L := L) hκ hrep.1
  refine ⟨l0, ?_, ?_⟩
  · intro l hl
    obtain ⟨hs1, -⟩ := hl0 l hl (cutSeq L l) (Or.inl rfl)
    obtain ⟨hs2, -⟩ := hl0 l hl (-cutSeq L l) (Or.inr rfl)
    have g1 := gap_ae hκ hu0 hrep hs1
    have g2 := gap_ae hκ hu0 hrep hs2
    rw [← hmeas] at g1 g2
    filter_upwards [g1, g2] with x hx1 hx2
    refine ⟨hx1, ?_⟩
    rwa [sub_neg_eq_add] at hx2
  · intro l hl w hw
    haveI : IsProbabilityMeasure (μ : Measure ℝ) := inferInstance
    obtain ⟨hs1, hd1⟩ := hl0 l hl (cutSeq L l) (Or.inl rfl)
    obtain ⟨hs2, hd2⟩ := hl0 l hl (-cutSeq L l) (Or.inr rfl)
    have g1 := gap_ae hκ hu0 hrep hs1
    have g2 := gap_ae hκ hu0 hrep hs2
    rw [← hmeas] at g1 g2
    have htrace := QuantumNLS.RootTraceSymbolFinal.traceSymbolIdentity hκ.le u
    have hΔ : Continuous fun z : ℂ => QuantumNLS.L2SpatialTransfer.discriminant κ u z :=
      (QuantumNLS.PhysicalUpperTraceIdentity.entire_discriminant κ u).continuous
    have hcos : ∀ z : ℂ, 0 < z.im →
        2 * Complex.cos (boundaryPhase L κ (μ : Measure ℝ) z) = QuantumNLS.L2SpatialTransfer.discriminant κ u z := by
      intro z hz
      rw [hmeas]
      exact QuantumNLS.PhysicalUpperTraceIdentity.upper_cosine hκ hu0 htrace hz
    have hnorm : ∀ c : ℝ, ‖QuantumNLS.L2SpatialTransfer.discriminant κ u (c : ℂ)‖ = |discReal L κ uf c| := by
      intro c
      rw [disc_eq_rep hrep κ (c : ℂ), QuantumNLS.RootDiscriminant.discriminant_eq_discReal L κ hrep.1 c,
        Complex.norm_real, Real.norm_eq_abs]
    exact norm_Dsrc_lower hκ hL (δ := 1 / L) (by positivity) hh g1 g2 hΔ hcos
      (by rw [hnorm]; exact hd1) (by rw [hnorm]; exact hd2) hw

/-- **`RootSpectralInputs` for the actual measure, from the even-moment input.**  Only `moments` (`EvenMoments`) is an input;
`gap` and `discr` are proved (for every height `h > 0`; in particular for `h > eta0`). -/
theorem rootSpectralInputs (hκ : 0 < κ) {u : L2T L} (hu : ‖u‖ = 1) {uf : ℝ → ℂ}
    (hrep : IsPeriodicRepresentative L u uf) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) (hmom : EvenMoments (μ : Measure ℝ)) {h : ℝ} (hh : 0 < h) :
    ∃ δ d0 : ℝ, 0 < δ ∧ 0 < d0 ∧ ∃ l0 : ℕ, RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0 := by
  have hL : 0 < L := Fact.out
  obtain ⟨l0, hg, hd⟩ := rootSpectralInputs_geometry hκ hu hrep hμ hh
  exact ⟨1 / L, dlow L κ (1 / L) h, by positivity, dlow_pos hκ hL (by positivity) hh, l0, hmom, hg, hd⟩

end Actual

end QuantumNLS.RootSpectralInputsDischarge

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RootSpectralInputsDischarge.measure_eq_limit
#print axioms QuantumNLS.RootSpectralInputsDischarge.sin_lower_cut
#print axioms QuantumNLS.RootSpectralInputsDischarge.norm_Dsrc_lower
#print axioms QuantumNLS.RootSpectralInputsDischarge.disc_small
#print axioms QuantumNLS.RootSpectralInputsDischarge.gap_ae
#print axioms QuantumNLS.RootSpectralInputsDischarge.rootSpectralInputs_geometry
#print axioms QuantumNLS.RootSpectralInputsDischarge.rootSpectralInputs
