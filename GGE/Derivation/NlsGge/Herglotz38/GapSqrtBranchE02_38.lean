import Mathlib

/-!
# Branch `gapSqrt a b` of `√((z-a)(z-b))` with cut exactly `[a,b]` (a ≤ b real)

`gapSqrt a b z = (z - b) * ((z - a)/(z - b))^(1/2)` (principal complex square root).
Proved: analytic on `ℂ \ [a,b]`; `gapSqrt^2 = (z-a)(z-b)` everywhere; sign on real axis
outside `[a,b]`; `gapSqrt z - z → -(a+b)/2` along `cocompact ℂ`; boundary value
`i √((λ-a)(b-λ))` from above on `(a,b)`; `Im gapSqrt > 0` on the upper half-plane.
The degenerate case `a = b` gives `gapSqrt a a z = z - a`.
-/

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

open Complex Filter Topology

/-- Branch of `√((z-a)(z-b))`, `a ≤ b` real: `(z-b) * √((z-a)/(z-b))` (principal square root). -/
noncomputable def gapSqrt (a b : ℝ) (z : ℂ) : ℂ :=
  (z - b) * ((z - a) / (z - b)) ^ ((2 : ℂ)⁻¹)

lemma sqrtC_sq (w : ℂ) : (w ^ ((2 : ℂ)⁻¹)) ^ 2 = w := Complex.cpow_ofNat_inv_pow w 2

lemma gapSqrt_sq (a b : ℝ) (z : ℂ) : gapSqrt a b z ^ 2 = (z - a) * (z - b) := by
  unfold gapSqrt
  by_cases h : z - b = 0
  · simp [h]
  · rw [mul_pow, sqrtC_sq]; field_simp

lemma ratio_mem_slitPlane {a b : ℝ} (hab : a ≤ b) {z : ℂ}
    (hz : z ∉ ((↑) : ℝ → ℂ) '' Set.Icc a b) : (z - a) / (z - b) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  have hzb : z - b ≠ 0 := by
    intro h
    apply hz
    refine ⟨b, ⟨hab, le_rfl⟩, ?_⟩
    exact (sub_eq_zero.mp h).symm
  have hN : 0 < Complex.normSq (z - b) := Complex.normSq_pos.mpr hzb
  rw [Complex.div_re, Complex.div_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  by_cases hy : z.im = 0
  · left
    have hx : z.re ∉ Set.Icc a b := by
      intro hx; apply hz; exact ⟨z.re, hx, by apply Complex.ext <;> simp [hy]⟩
    have hpos : 0 < (z.re - a) * (z.re - b) := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · nlinarith
      · nlinarith
    have : 0 < (z.re - a) * (z.re - b) + z.im * z.im := by rw [hy]; linarith
    have h2 : 0 < ((z.re - a) * (z.re - b) + z.im * z.im) / Complex.normSq (z - b) := div_pos this hN
    rw [add_div] at h2
    simpa [Complex.sub_re, Complex.sub_im] using h2
  · by_cases hab' : a = b
    · left
      subst hab'
      have : 0 < (z.re - a) * (z.re - a) + z.im * z.im := by
        have := mul_self_pos.mpr hy; nlinarith [mul_self_nonneg (z.re - a)]
      have h2 := div_pos this hN
      rw [add_div] at h2
      simpa [Complex.sub_re, Complex.sub_im] using h2
    · right
      have hne : a - b ≠ 0 := sub_ne_zero.mpr hab'
      have : z.im * (z.re - b) - (z.re - a) * z.im = z.im * (a - b) := by ring
      intro h0
      rw [← sub_div] at h0
      have h1 : (z.im * (z.re - b) - (z.re - a) * z.im) = 0 := by
        rcases div_eq_zero_iff.mp h0 with h | h
        · simpa using h
        · exact absurd h hN.ne'
      rw [this] at h1
      rcases mul_eq_zero.mp h1 with h | h
      · exact hy h
      · exact hne h


lemma differentiableOn_gapSqrt {a b : ℝ} (hab : a ≤ b) :
    DifferentiableOn ℂ (gapSqrt a b) (((↑) : ℝ → ℂ) '' Set.Icc a b)ᶜ := by
  intro z hz
  have hzb : z - b ≠ 0 := by
    intro h
    apply hz
    exact ⟨b, ⟨hab, le_rfl⟩, (sub_eq_zero.mp h).symm⟩
  have hr := ratio_mem_slitPlane hab hz
  apply DifferentiableAt.differentiableWithinAt
  unfold gapSqrt
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (z - a) / (z - b)) z :=
    ((differentiableAt_id.sub_const _).div (differentiableAt_id.sub_const _) hzb)
  exact (differentiableAt_id.sub_const _).mul (h1.cpow_const hr)

lemma sqrtC_ofReal {r : ℝ} (hr : 0 ≤ r) :
    ((r : ℂ)) ^ ((2 : ℂ)⁻¹) = ((r ^ (2⁻¹ : ℝ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow hr]; push_cast; rfl

lemma gapSqrt_real {a b : ℝ} (hab : a ≤ b) (x : ℝ) (hx : x < a ∨ b < x) :
    ∃ r : ℝ, 0 < r ∧ gapSqrt a b x = ((x - b) * r : ℝ) := by
  have hq : 0 < (x - a) / (x - b) := by
    rcases hx with h | h
    · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    · exact div_pos (by linarith) (by linarith)
  refine ⟨((x - a) / (x - b)) ^ (2⁻¹ : ℝ), Real.rpow_pos_of_pos hq _, ?_⟩
  unfold gapSqrt
  have : ((x : ℂ) - a) / ((x : ℂ) - b) = (((x - a) / (x - b) : ℝ) : ℂ) := by push_cast; rfl
  rw [this, sqrtC_ofReal hq.le]; push_cast; rfl

lemma gapSqrt_pos_right {a b : ℝ} (hab : a ≤ b) (x : ℝ) (hx : b < x) :
    0 < (gapSqrt a b x).re ∧ (gapSqrt a b x).im = 0 := by
  obtain ⟨r, hr, h⟩ := gapSqrt_real hab x (Or.inr hx)
  rw [h]; simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  exact mul_pos (by linarith) hr

lemma gapSqrt_neg_left {a b : ℝ} (hab : a ≤ b) (x : ℝ) (hx : x < a) :
    (gapSqrt a b x).re < 0 ∧ (gapSqrt a b x).im = 0 := by
  obtain ⟨r, hr, h⟩ := gapSqrt_real hab x (Or.inl hx)
  rw [h]; simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  exact mul_neg_of_neg_of_pos (by linarith) hr


lemma sqrtC_re_nonneg (w : ℂ) : 0 ≤ (w ^ ((2 : ℂ)⁻¹)).re := by
  by_cases hw : w = 0
  · subst hw; simp
  · rw [Complex.cpow_def_of_ne_zero hw, Complex.exp_re]
    apply mul_nonneg (Real.exp_pos _).le
    have him : (Complex.log w * (2 : ℂ)⁻¹).im = Complex.arg w / 2 := by
      simp [Complex.log_im]; ring
    rw [him]
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have := Complex.neg_pi_lt_arg w; linarith
    · have := Complex.arg_le_pi w; linarith

lemma gapSqrt_sub_id_eq (a b : ℝ) {z : ℂ} (hz : z ≠ b) :
    gapSqrt a b z - z = ((b : ℂ) - a) / (((z - a) / (z - b)) ^ ((2 : ℂ)⁻¹) + 1) - b := by
  have hzb : z - b ≠ 0 := sub_ne_zero.mpr hz
  set t := ((z - a) / (z - b)) ^ ((2 : ℂ)⁻¹) with ht
  have ht2 : t ^ 2 = (z - a) / (z - b) := sqrtC_sq _
  have ht1 : t + 1 ≠ 0 := by
    intro h
    have := sqrtC_re_nonneg ((z - a) / (z - b))
    rw [← ht] at this
    have h2 : t.re + 1 = 0 := by simpa using congrArg Complex.re h
    linarith
  have key : (z - b) * (t ^ 2 - 1) = (b : ℂ) - a := by
    rw [ht2]; field_simp; ring
  unfold gapSqrt
  rw [← ht]
  field_simp
  linear_combination key

/-- Asymptotics: `gapSqrt a b z - z → -(a+b)/2` as `‖z‖ → ∞`. -/
theorem gapSqrt_sub_id_tendsto (a b : ℝ) :
    Tendsto (fun z : ℂ => gapSqrt a b z - z) (cocompact ℂ)
      (𝓝 (-(((a : ℂ) + (b : ℂ)) / 2))) := by
  have hinv : Tendsto (fun z : ℂ => (z - b)⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded.comp (tendsto_sub_const_cobounded (b : ℂ))
  have hne : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ b := by
    have := (isCompact_singleton (x := (b : ℂ))).compl_mem_cocompact
    filter_upwards [this] with z hz using hz
  have hρ : Tendsto (fun z : ℂ => (z - a) / (z - b)) (cocompact ℂ) (𝓝 1) := by
    have h1 : Tendsto (fun z : ℂ => 1 + ((b : ℂ) - a) * (z - b)⁻¹) (cocompact ℂ) (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℂ))).add (hinv.const_mul ((b : ℂ) - a))
    refine h1.congr' ?_
    filter_upwards [hne] with z hz
    have : z - b ≠ 0 := sub_ne_zero.mpr hz
    field_simp; ring
  have ht : Tendsto (fun z : ℂ => ((z - a) / (z - b)) ^ ((2 : ℂ)⁻¹)) (cocompact ℂ) (𝓝 1) := by
    have hc : ContinuousAt (fun w : ℂ => w ^ ((2 : ℂ)⁻¹)) 1 :=
      continuousAt_cpow_const (by simp)
    have := hc.tendsto.comp hρ
    simpa [Function.comp_def] using this
  have hlim : Tendsto (fun z : ℂ => ((b : ℂ) - a) / (((z - a) / (z - b)) ^ ((2 : ℂ)⁻¹) + 1) - b)
      (cocompact ℂ) (𝓝 (-(((a : ℂ) + (b : ℂ)) / 2))) := by
    have h2 : Tendsto (fun z : ℂ => ((z - a) / (z - b)) ^ ((2 : ℂ)⁻¹) + 1) (cocompact ℂ) (𝓝 2) := by
      simpa [one_add_one_eq_two] using ht.add_const 1
    have h3 := ((tendsto_const_nhds (x := ((b : ℂ) - a))).div h2 (by norm_num)).sub_const (b : ℂ)
    convert h3 using 2
    ring
  refine hlim.congr' ?_
  filter_upwards [hne] with z hz
  exact (gapSqrt_sub_id_eq a b hz).symm


lemma ratio_im_neg {a b lam ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    (((lam : ℂ) + (ε : ℂ) * Complex.I - a) / ((lam : ℂ) + (ε : ℂ) * Complex.I - b)).im < 0 := by
  have hne : ((lam : ℂ) + (ε : ℂ) * Complex.I - b) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hN : 0 < Complex.normSq ((lam : ℂ) + (ε : ℂ) * Complex.I - b) := Complex.normSq_pos.mpr hne
  rw [Complex.div_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [← sub_div]
  apply div_neg_of_neg_of_pos _ (by simpa using hN)
  nlinarith

lemma sqrtC_of_im_neg {w : ℂ} (hw : w.im < 0) :
    w ^ ((2 : ℂ)⁻¹) = -Complex.I * (-w) ^ ((2 : ℂ)⁻¹) := by
  have h0 : w ≠ 0 := fun h => by simp [h] at hw
  have h0' : -w ≠ 0 := neg_ne_zero.mpr h0
  have hlog : Complex.log (-w) = Complex.log w + Real.pi * Complex.I := by
    rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg hw]
    push_cast; ring
  rw [Complex.cpow_def_of_ne_zero h0, Complex.cpow_def_of_ne_zero h0', hlog, add_mul, Complex.exp_add]
  have : (Real.pi : ℂ) * Complex.I * (2 : ℂ)⁻¹ = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_mul_I]
  have hc : Complex.cos ((Real.pi / 2 : ℝ) : ℂ) = 0 := by
    rw [← Complex.ofReal_cos, Real.cos_pi_div_two]; simp
  have hs : Complex.sin ((Real.pi / 2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sin, Real.sin_pi_div_two]; simp
  rw [hc, hs]
  have : -Complex.I * (Complex.exp (Complex.log w * 2⁻¹) * (0 + 1 * Complex.I))
      = - (Complex.I * Complex.I) * Complex.exp (Complex.log w * 2⁻¹) := by ring
  rw [this, Complex.I_mul_I]; simp

lemma real_sqrt_aux {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (u : ℂ) * ((((v / u : ℝ)) ^ (2⁻¹ : ℝ) : ℝ) : ℂ) = ((Real.sqrt (v * u) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  rw [show (2⁻¹ : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  rw [show v * u = (u * u) * (v / u) by field_simp, Real.sqrt_mul (mul_self_nonneg u),
    Real.sqrt_mul_self hu.le]

/-- Boundary value from above on the open gap. -/
theorem gapSqrt_boundary_above {a b : ℝ} {lam : ℝ} (hl : lam ∈ Set.Ioo a b) :
    Tendsto (fun ε : ℝ => gapSqrt a b ((lam : ℂ) + (ε : ℂ) * Complex.I)) (𝓝[>] 0)
      (𝓝 (Complex.I * ((Real.sqrt ((lam - a) * (b - lam)) : ℝ) : ℂ))) := by
  obtain ⟨hla, hlb⟩ := hl
  set F : ℝ → ℂ := fun ε =>
    (((lam : ℂ) + (ε : ℂ) * Complex.I) - b) * (-Complex.I) *
      (-(((lam : ℂ) + (ε : ℂ) * Complex.I - a) / ((lam : ℂ) + (ε : ℂ) * Complex.I - b))) ^ ((2 : ℂ)⁻¹)
    with hF
  have hden : (lam : ℂ) + ((0 : ℝ) : ℂ) * Complex.I - b ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this; linarith
  have hq : 0 < (lam - a) / (b - lam) := div_pos (by linarith) (by linarith)
  have hval : (-(((lam : ℂ) + ((0 : ℝ) : ℂ) * Complex.I - a) / ((lam : ℂ) + ((0 : ℝ) : ℂ) * Complex.I - b)))
      = (((lam - a) / (b - lam) : ℝ) : ℂ) := by
    have : (b : ℂ) - lam ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h2 : (lam : ℂ) - b ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    push_cast
    simp
    field_simp
    ring
  have hcont : ContinuousAt F 0 := by
    have hin : ContinuousAt (fun ε : ℝ =>
        (-(((lam : ℂ) + (ε : ℂ) * Complex.I - a) / ((lam : ℂ) + (ε : ℂ) * Complex.I - b)))) 0 := by
      apply ContinuousAt.neg
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · exact hden
    have hslit : (-(((lam : ℂ) + ((0 : ℝ) : ℂ) * Complex.I - a) / ((lam : ℂ) + ((0 : ℝ) : ℂ) * Complex.I - b)))
        ∈ Complex.slitPlane := by
      rw [hval]; exact Complex.ofReal_mem_slitPlane.mpr hq
    have hin' : ContinuousAt (fun ε : ℝ =>
        (((lam : ℂ) + (ε : ℂ) * Complex.I - a) / ((lam : ℂ) + (ε : ℂ) * Complex.I - b))) 0 := by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · exact hden
    have hc : ContinuousAt (fun w : ℂ => (-w) ^ ((2 : ℂ)⁻¹))
        (((lam : ℂ) + ((0 : ℝ) : ℂ) * Complex.I - a) / ((lam : ℂ) + ((0 : ℝ) : ℂ) * Complex.I - b)) :=
      (continuousAt_cpow_const (b := (2 : ℂ)⁻¹) hslit).comp_of_eq continuous_neg.continuousAt rfl
    have hsq := hc.comp_of_eq hin' rfl
    have hlin : ContinuousAt (fun ε : ℝ =>
        (((lam : ℂ) + (ε : ℂ) * Complex.I) - b) * (-Complex.I)) 0 := by fun_prop
    exact hlin.mul hsq
  have hF0 : F 0 = Complex.I * ((Real.sqrt ((lam - a) * (b - lam)) : ℝ) : ℂ) := by
    simp only [hF]
    rw [hval, sqrtC_ofReal hq.le]
    have := real_sqrt_aux (u := b - lam) (v := lam - a) (by linarith) (by linarith)
    rw [← this]
    push_cast
    simp
    ring
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, gapSqrt a b ((lam : ℂ) + (ε : ℂ) * Complex.I) = F ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    simp only [hF]
    unfold gapSqrt
    rw [sqrtC_of_im_neg (ratio_im_neg (lam := lam) (by linarith) hε'), mul_assoc]
  have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  rw [hF0] at this
  exact this.congr' (hev.mono fun ε h => h.symm)


lemma gapSqrt_im_ne_zero (a b : ℝ) {z : ℂ} (hz : 0 < z.im) : (gapSqrt a b z).im ≠ 0 := by
  intro h
  have h2 := gapSqrt_sq a b z
  have him : (((z - a) * (z - b) : ℂ)).im = 0 := by
    rw [← h2, pow_two, Complex.mul_im, h]; ring
  have hre : 0 ≤ (((z - a) * (z - b) : ℂ)).re := by
    rw [← h2, pow_two, Complex.mul_re, h]; nlinarith [mul_self_nonneg (gapSqrt a b z).re]
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero] at him hre
  have hx : 2 * z.re = a + b := by
    have : z.im * (2 * z.re - a - b) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hz.ne'
    · linarith
  have : z.re - a = - (z.re - b) := by linarith
  rw [this] at hre
  nlinarith [mul_self_nonneg (z.re - b), mul_pos hz hz]

/-- Positivity of the imaginary part in the open upper half-plane (`a ≤ b`). -/
theorem gapSqrt_im_pos {a b : ℝ} (hab : a ≤ b) {z : ℂ} (hz : 0 < z.im) :
    0 < (gapSqrt a b z).im := by
  have hUHP : Convex ℝ {c : ℂ | 0 < c.im} := convex_halfSpace_im_gt 0
  have hcont : ContinuousOn (fun c : ℂ => (gapSqrt a b c).im) {c : ℂ | 0 < c.im} := by
    have hd : DifferentiableOn ℂ (gapSqrt a b) {c : ℂ | 0 < c.im} := by
      refine (differentiableOn_gapSqrt hab).mono ?_
      intro c hc hc'
      obtain ⟨x, _, rfl⟩ := hc'
      simp at hc
    exact Complex.continuous_im.comp_continuousOn hd.continuousOn
  -- a point in the upper half-plane with positive imaginary part of the branch
  have hasy := gapSqrt_sub_id_tendsto a b
  have hit : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) atTop (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    simpa using tendsto_abs_atTop_atTop
  have hlim := (Complex.continuous_im.tendsto _).comp (hasy.comp hit)
  have hev := hlim.eventually (Metric.ball_mem_nhds _ (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨y, hy1, hy2⟩ := (hev.and (eventually_gt_atTop (2 : ℝ))).exists
  have hy1' : |(gapSqrt a b ((y : ℂ) * Complex.I) - (y : ℂ) * Complex.I).im - (-(((a : ℂ) + b) / 2)).im| < 1 := by
    simpa [Real.dist_eq] using hy1
  have hpos : 0 < (gapSqrt a b ((y : ℂ) * Complex.I)).im := by
    have := (abs_lt.mp hy1').1
    simp at this
    linarith
  by_contra hneg
  have hneg := not_lt.mp hneg
  have hmem1 : z ∈ {c : ℂ | 0 < c.im} := hz
  have hmem2 : ((y : ℂ) * Complex.I) ∈ {c : ℂ | 0 < c.im} := by
    show 0 < ((y : ℂ) * Complex.I).im
    simp; linarith
  obtain ⟨u, hu, hu0⟩ := hUHP.isPreconnected.intermediate_value hmem1 hmem2 hcont
    (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨hneg, hpos.le⟩)
  exact gapSqrt_im_ne_zero a b hu hu0


lemma isOpen_gapCut_compl (a b : ℝ) : IsOpen (((↑) : ℝ → ℂ) '' Set.Icc a b)ᶜ :=
  (isCompact_Icc.image Complex.continuous_ofReal).isClosed.isOpen_compl

theorem analyticOnNhd_gapSqrt {a b : ℝ} (hab : a ≤ b) :
    AnalyticOnNhd ℂ (gapSqrt a b) (((↑) : ℝ → ℂ) '' Set.Icc a b)ᶜ :=
  (differentiableOn_gapSqrt hab).analyticOnNhd (isOpen_gapCut_compl a b)

/-- The degenerate case. -/
lemma gapSqrt_self (a : ℝ) (z : ℂ) : gapSqrt a a z = z - a := by
  unfold gapSqrt
  by_cases h : z - a = 0
  · simp [h]
  · rw [div_self h]; simp

end NlsGge.SpectralFoundations
