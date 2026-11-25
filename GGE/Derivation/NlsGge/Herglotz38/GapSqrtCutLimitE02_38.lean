import Mathlib
import NlsGge.Herglotz38.GapSqrtBranchE02_38

set_option autoImplicit false

/-!
# Upper half-plane limit of `gapSqrt` at an interior cut point

For `x₀ ∈ (a,b)`, near `x₀` and in the open upper half-plane,
`gapSqrt a b z = I * (-(z-a)(z-b))^(1/2)` with the principal branch, and consequently
`gapSqrt a b z → I * sqrt((x₀-a)(b-x₀))` as `z → x₀` within `Im z > 0`.
-/

namespace NlsGge.SpectralFoundations

open Complex Filter Topology

lemma cutQ_continuous (a b : ℝ) :
    Continuous (fun z : ℂ => -((z - a) * (z - b))) := by fun_prop

lemma cutQ_at_cut {a b x₀ : ℝ} :
    -(((x₀ : ℂ) - a) * ((x₀ : ℂ) - b)) = (((x₀ - a) * (b - x₀) : ℝ) : ℂ) := by
  push_cast; ring

lemma cutQ_mem_slitPlane_at_cut {a b x₀ : ℝ} (hx : x₀ ∈ Set.Ioo a b) :
    -(((x₀ : ℂ) - a) * ((x₀ : ℂ) - b)) ∈ Complex.slitPlane := by
  rw [cutQ_at_cut]
  apply Complex.ofReal_mem_slitPlane.mpr
  exact mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)

theorem gapSqrt_eq_I_mul_cpow_near_cut_E02_38 {a b x₀ : ℝ} (hx : x₀ ∈ Set.Ioo a b) :
    ∃ r > 0, (∀ z ∈ Metric.ball (x₀ : ℂ) r, -((z - a) * (z - b)) ∈ Complex.slitPlane) ∧
      (∀ z ∈ Metric.ball (x₀ : ℂ) r, 0 < z.im →
        gapSqrt a b z = Complex.I * (-((z - a) * (z - b))) ^ (2⁻¹ : ℂ)) := by
  have hab : a ≤ b := (hx.1.trans hx.2).le
  have hopen : IsOpen {z : ℂ | -((z - a) * (z - b)) ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage (cutQ_continuous a b)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (x₀ : ℂ) (cutQ_mem_slitPlane_at_cut hx)
  refine ⟨r, hr, fun z hz => hball hz, ?_⟩
  intro z hz him
  set w : ℂ := (-((z - a) * (z - b))) ^ (2⁻¹ : ℂ) with hw
  have hw2 : w ^ 2 = -((z - a) * (z - b)) := Complex.cpow_ofNat_inv_pow _ 2
  have hre : 0 ≤ w.re := sqrtC_re_nonneg _
  have hpos : 0 < (gapSqrt a b z).im := gapSqrt_im_pos hab him
  have hprod : (gapSqrt a b z - Complex.I * w) * (gapSqrt a b z + Complex.I * w) = 0 := by
    have h := gapSqrt_sq a b z
    have : (gapSqrt a b z - Complex.I * w) * (gapSqrt a b z + Complex.I * w)
        = gapSqrt a b z ^ 2 + w ^ 2 := by
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination (-(w ^ 2)) * hI
    rw [this, h, hw2]; ring
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have h' : gapSqrt a b z = -(Complex.I * w) := eq_neg_of_add_eq_zero_left h
    have : (gapSqrt a b z).im = -w.re := by rw [h']; simp
    linarith

theorem I_mul_cpow_at_cut_E02_38 {a b x₀ : ℝ} (hx : x₀ ∈ Set.Ioo a b) :
    Complex.I * (-(((x₀ : ℂ) - a) * ((x₀ : ℂ) - b))) ^ (2⁻¹ : ℂ)
      = Complex.I * ((Real.sqrt ((x₀ - a) * (b - x₀)) : ℝ) : ℂ) := by
  rw [cutQ_at_cut, sqrtC_ofReal (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)).le,
    Real.sqrt_eq_rpow, one_div]

theorem tendsto_gapSqrt_nhdsWithin_cut_E02_38 {a b x₀ : ℝ} (hx : x₀ ∈ Set.Ioo a b) :
    Tendsto (gapSqrt a b) (𝓝[{z : ℂ | 0 < z.im}] (x₀ : ℂ))
      (𝓝 (Complex.I * ((Real.sqrt ((x₀ - a) * (b - x₀)) : ℝ) : ℂ))) := by
  obtain ⟨r, hr, hslit, heq⟩ := gapSqrt_eq_I_mul_cpow_near_cut_E02_38 hx
  have hcont : ContinuousAt
      (fun z : ℂ => Complex.I * (-((z - a) * (z - b))) ^ (2⁻¹ : ℂ)) (x₀ : ℂ) := by
    have h1 : ContinuousAt (fun z : ℂ => -((z - a) * (z - b))) (x₀ : ℂ) :=
      (cutQ_continuous a b).continuousAt
    exact continuousAt_const.mul
      (h1.cpow continuousAt_const (cutQ_mem_slitPlane_at_cut hx))
  have hT : Tendsto (fun z : ℂ => Complex.I * (-((z - a) * (z - b))) ^ (2⁻¹ : ℂ))
      (𝓝[{z : ℂ | 0 < z.im}] (x₀ : ℂ))
      (𝓝 (Complex.I * (-(((x₀ : ℂ) - a) * ((x₀ : ℂ) - b))) ^ (2⁻¹ : ℂ))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  rw [I_mul_cpow_at_cut_E02_38 hx] at hT
  refine hT.congr' ?_
  have hmem : Metric.ball (x₀ : ℂ) r ∈ 𝓝[{z : ℂ | 0 < z.im}] (x₀ : ℂ) :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hr)
  have hmem2 : {z : ℂ | 0 < z.im} ∈ 𝓝[{z : ℂ | 0 < z.im}] (x₀ : ℂ) := self_mem_nhdsWithin
  filter_upwards [hmem, hmem2] with z hz hz2 using (heq z hz hz2).symm

end NlsGge.SpectralFoundations
