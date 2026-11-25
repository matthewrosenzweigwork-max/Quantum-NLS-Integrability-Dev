import Mathlib

/-!
# R-0908DFDE `prop:root-gap-multiplicity` (`ROOT_gap_multiplicity.tex:8`): abstract local analysis

Abstract setting (nothing about Bethe states): `Δ : ℂ → ℂ` entire, real on `ℝ`; for `Im z > 0` there is a phase `γ` with `2 cos γ = Δ` and `Im γ ≥ L Im z / 2 > 0`.

* `zeros_real`: every zero of `Δ² - 4` is real (upper half-plane: `cos γ = ±1` forces `γ ∈ πℤ`; lower half-plane: Schwarz reflection).
* For a real zero `x₀` (`Δ(x₀) = 2σ`, `σ = ±1`) at which the phase tends to `nπ`, `σ = (-1)^n`, along the vertical ray (`Ray` data, `w = (γ - nπ)/2`,
  `Δ - 2σ = -4σ sin² w`, `Im w ≥ L y / 4`):
  * `lower_bound`: `|Δ(x₀ + iy) - 2σ| ≥ L² y² / 4`;
  * `order_le_two`, `order_cases`: the analytic order of `Δ - 2σ` at `x₀` is `1` or `2`;
  * `double_strict`: order `2` gives `|Δ| < 2` immediately on both sides (the printed `v = a (z - x₀) + ...`, `a ≥ L/2`, argument replaced by the vertical-ray limit);
  * `simple_sides`: order `1` gives `|Δ| > 2` on one full side and `|Δ| < 2` on the other.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace QuantumNLS.RootGapLocal

theorem norm_sin_sq (w : ℂ) : ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sin_eq]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sin_ofReal_re,
    Complex.sin_ofReal_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.cosh_ofReal_re,
    Complex.cosh_ofReal_im, Complex.sinh_ofReal_re, Complex.sinh_ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, sub_zero, add_zero, mul_one, zero_sub, neg_mul, mul_neg, neg_neg]
  linear_combination Real.sin w.re ^ 2 * Real.cosh_sq w.im +
    Real.sinh w.im ^ 2 * Real.sin_sq_add_cos_sq w.re

theorem sinh_sq_le (w : ℂ) {b : ℝ} (hb : 0 ≤ b) (hw : b ≤ w.im) : b ^ 2 ≤ ‖Complex.sin w‖ ^ 2 := by
  rw [norm_sin_sq]
  have h1 : b ≤ Real.sinh w.im := le_trans (Real.self_le_sinh_iff.2 hb) (Real.sinh_le_sinh.2 hw)
  have := pow_le_pow_left₀ hb h1 2
  nlinarith [sq_nonneg (Real.sin w.re)]

/-! ## Reality of the zeros of `Δ² - 4` -/

theorem schwarz {Δ : ℂ → ℂ} (hΔ : Differentiable ℂ Δ) (hreal : ∀ x : ℝ, (Δ (x : ℂ)).im = 0) (z : ℂ) :
    Δ (conj z) = conj (Δ z) := by
  set g : ℂ → ℂ := fun z => conj (Δ (conj z)) with hg
  have hgd : Differentiable ℂ g := by
    intro z
    have := (hΔ (conj z)).conj_conj
    simpa [hg, Function.comp_def] using this
  have hfa : AnalyticOnNhd ℂ Δ univ := fun z _ => hΔ.analyticAt z
  have hga : AnalyticOnNhd ℂ g univ := fun z _ => hgd.analyticAt z
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), Δ z = g z := by
    have hmap : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
    have hall : ∀ x : ℝ, Δ (x : ℂ) = g (x : ℂ) := by
      intro x
      have hc : conj (Δ (x : ℂ)) = Δ (x : ℂ) := Complex.conj_eq_iff_im.2 (hreal x)
      simp [hg, hc]
    exact hmap.frequently (Eventually.of_forall hall).frequently
  have := hfa.eqOn_of_preconnected_of_frequently_eq hga isPreconnected_univ (mem_univ 0) hfreq (mem_univ (conj z))
  have h2 : Δ (conj z) = conj (Δ (conj (conj z))) := this
  simpa using h2

theorem zeros_real {Δ γ : ℂ → ℂ} (hΔ : Differentiable ℂ Δ) (hreal : ∀ x : ℝ, (Δ (x : ℂ)).im = 0)
    (hcos : ∀ z : ℂ, 0 < z.im → 2 * Complex.cos (γ z) = Δ z)
    (hpos : ∀ z : ℂ, 0 < z.im → 0 < (γ z).im) {z : ℂ} (hz : Δ z ^ 2 - 4 = 0) : z.im = 0 := by
  have upper : ∀ z : ℂ, 0 < z.im → Δ z ^ 2 - 4 ≠ 0 := by
    intro z hz0 h0
    have hc : Complex.cos (γ z) ^ 2 = 1 := by
      have : (2 * Complex.cos (γ z)) ^ 2 = 4 := by rw [hcos z hz0]; linear_combination h0
      linear_combination this / 4
    have hs : Complex.sin (γ z) = 0 := by
      have := Complex.sin_sq_add_cos_sq (γ z)
      have h2 : Complex.sin (γ z) ^ 2 = 0 := by linear_combination this - hc
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h2
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 hs
    have := hpos z hz0
    rw [hk] at this
    simp at this
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply upper (conj z) (by simpa using hlt)
    rw [schwarz hΔ hreal z, ← map_pow, ← map_ofNat conj 4, ← map_sub, hz, map_zero]
  · exact upper z hgt hz

/-! ## Local classification at a real zero -/

section Local

variable {Δ : ℂ → ℂ} {L σ : ℝ} {x0 : ℝ}

/-- Vertical-ray data at `x₀`: `w = (γ - nπ)/2 → 0`, `Im w ≥ L y / 4`, `Δ - 2σ = -4σ sin² w`. -/
def Ray (Δ : ℂ → ℂ) (L σ x0 : ℝ) : Prop :=
  ∃ w : ℝ → ℂ, Tendsto w (𝓝[>] 0) (𝓝 0) ∧ (∀ y : ℝ, 0 < y → L * y / 4 ≤ (w y).im) ∧
    ∀ y : ℝ, 0 < y → Δ ((x0 : ℂ) + (y : ℂ) * Complex.I) - 2 * (σ : ℂ) = -4 * (σ : ℂ) * Complex.sin (w y) ^ 2

theorem lower_bound (hσ : σ = 1 ∨ σ = -1) (hL : 0 < L) (hray : Ray Δ L σ x0) :
    ∀ y : ℝ, 0 < y → L ^ 2 * y ^ 2 / 4 ≤ ‖Δ ((x0 : ℂ) + (y : ℂ) * Complex.I) - 2 * (σ : ℂ)‖ := by
  obtain ⟨w, -, hwim, hw⟩ := hray
  intro y hy
  rw [hw y hy, norm_mul, norm_mul, norm_pow]
  have hσn : ‖(σ : ℂ)‖ = 1 := by rcases hσ with h | h <;> simp [h]
  have h4 : ‖(-4 : ℂ)‖ = 4 := by simp
  rw [h4, hσn]
  have hLy : L * y / 4 ≤ (w y).im := hwim y hy
  have hLy0 : 0 ≤ L * y / 4 := by positivity
  have := sinh_sq_le (w y) hLy0 hLy
  nlinarith

theorem analytic_f (hΔ : Differentiable ℂ Δ) (z : ℂ) :
    AnalyticAt ℂ (fun z => Δ z - 2 * (σ : ℂ)) z :=
  ((hΔ.sub_const (2 * (σ : ℂ)))).analyticAt z

theorem ray_tendsto (x0 : ℝ) :
    Tendsto (fun y : ℝ => (x0 : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (x0 : ℂ)) := by
  have hc : Continuous fun y : ℝ => (x0 : ℂ) + (y : ℂ) * Complex.I := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem order_le_two (hΔ : Differentiable ℂ Δ) (hσ : σ = 1 ∨ σ = -1) (hL : 0 < L) (hray : Ray Δ L σ x0) :
    analyticOrderAt (fun z => Δ z - 2 * (σ : ℂ)) (x0 : ℂ) ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have h3 : ((3 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun z => Δ z - 2 * (σ : ℂ)) (x0 : ℂ) := by
    have := (ENat.add_one_le_iff (by decide)).2 hlt
    calc ((3 : ℕ) : ℕ∞) = 2 + 1 := by norm_num
      _ ≤ _ := this
  obtain ⟨g, hg, hev⟩ := (natCast_le_analyticOrderAt (analytic_f hΔ _)).1 h3
  have hbound : ∀ᶠ z in 𝓝 (x0 : ℂ), ‖g z‖ < ‖g (x0 : ℂ)‖ + 1 :=
    hg.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))
  set C : ℝ := ‖g (x0 : ℂ)‖ + 1 with hC
  have hCpos : 0 < C := by positivity
  have E2 := (ray_tendsto x0).eventually (hev.and hbound)
  set ε : ℝ := L ^ 2 / (8 * C) with hε
  have hεpos : 0 < ε := by positivity
  have E3 : ∀ᶠ y : ℝ in 𝓝[>] 0, y < ε := (gt_mem_nhds hεpos).filter_mono nhdsWithin_le_nhds
  have E1 : ∀ᶠ y : ℝ in 𝓝[>] 0, 0 < y := eventually_mem_nhdsWithin
  obtain ⟨y, hy1, ⟨hy2, hy2'⟩, hy3⟩ := (E1.and (E2.and E3)).exists
  have hy : 0 < y := hy1
  have hlow := lower_bound hσ hL hray y hy
  rw [hy2] at hlow
  have hr : ((x0 : ℂ) + (y : ℂ) * Complex.I) - (x0 : ℂ) = (y : ℂ) * Complex.I := by ring
  rw [hr, smul_eq_mul, norm_mul, norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hy] at hlow
  have hg' := hy2'.le
  have h1 : y ^ 3 * ‖g ((x0 : ℂ) + (y : ℂ) * Complex.I)‖ ≤ y ^ 3 * C := by
    exact mul_le_mul_of_nonneg_left hg' (by positivity)
  have h2 : L ^ 2 * y ^ 2 / 4 ≤ y ^ 3 * C := le_trans hlow h1
  have h3 : L ^ 2 / 4 ≤ y * C := by
    have : y ^ 2 * (L ^ 2 / 4) ≤ y ^ 2 * (y * C) := by nlinarith [h2]
    exact le_of_mul_le_mul_left this (by positivity)
  have h4 : y * C < ε * C := mul_lt_mul_of_pos_right hy3 hCpos
  have h5 : ε * C = L ^ 2 / 8 := by rw [hε]; field_simp
  nlinarith [sq_nonneg L, h3, h4, h5, sq_pos_of_pos hL]

theorem order_cases (hΔ : Differentiable ℂ Δ) (hσ : σ = 1 ∨ σ = -1) (hL : 0 < L) (hray : Ray Δ L σ x0)
    (hx0 : Δ (x0 : ℂ) = 2 * (σ : ℂ)) :
    analyticOrderAt (fun z => Δ z - 2 * (σ : ℂ)) (x0 : ℂ) = 1 ∨
      analyticOrderAt (fun z => Δ z - 2 * (σ : ℂ)) (x0 : ℂ) = 2 := by
  have hle := order_le_two hΔ hσ hL hray
  have hne : analyticOrderAt (fun z => Δ z - 2 * (σ : ℂ)) (x0 : ℂ) ≠ 0 :=
    analyticOrderAt_ne_zero.2 ⟨analytic_f hΔ _, by simp [hx0]⟩
  have htop : analyticOrderAt (fun z => Δ z - 2 * (σ : ℂ)) (x0 : ℂ) ≠ ⊤ :=
    ne_top_of_le_ne_top (by decide) hle
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  rw [← hn] at hne hle ⊢
  have h2 : n ≤ 2 := by exact_mod_cast hle
  have h0 : n ≠ 0 := by
    intro h; apply hne; simp [h]
  rcases (by omega : n = 1 ∨ n = 2) with h | h <;> simp [h]

/-! ### The expansion `Δ - 2σ = (z - x₀)^n h(z)` on the real axis -/

theorem real_expansion (hreal : ∀ x : ℝ, (Δ (x : ℂ)).im = 0) {n : ℕ} {h : ℂ → ℂ}
    (hev : ∀ᶠ z in 𝓝 (x0 : ℂ), Δ z - 2 * (σ : ℂ) = (z - x0) ^ n • h z) :
    ∀ᶠ x : ℝ in 𝓝 x0, (Δ (x : ℂ)).re - 2 * σ = (x - x0) ^ n * (h (x : ℂ)).re ∧
      (x - x0) ^ n * (h (x : ℂ)).im = 0 := by
  filter_upwards [(Complex.continuous_ofReal.tendsto x0).eventually hev] with x hx
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (x - x0) ^ n := ⟨_, rfl⟩
  have e : Δ (x : ℂ) - 2 * (σ : ℂ) = (r : ℂ) * h (x : ℂ) := by
    rw [hx, smul_eq_mul, hr]; push_cast; ring
  have hre := congrArg Complex.re e
  have him := congrArg Complex.im e
  rw [Complex.re_ofReal_mul] at hre
  rw [Complex.im_ofReal_mul] at him
  have h1 : (Δ (x : ℂ) - 2 * (σ : ℂ)).re = (Δ (x : ℂ)).re - 2 * σ := by simp
  have h2 : (Δ (x : ℂ) - 2 * (σ : ℂ)).im = 0 := by simp [hreal x]
  rw [← hr]
  refine ⟨by rw [← h1, hre], by rw [← him, h2]⟩

theorem im_h_zero (hreal : ∀ x : ℝ, (Δ (x : ℂ)).im = 0) {n : ℕ} {h : ℂ → ℂ}
    (hh : ContinuousAt h (x0 : ℂ))
    (hev : ∀ᶠ z in 𝓝 (x0 : ℂ), Δ z - 2 * (σ : ℂ) = (z - x0) ^ n • h z) : (h (x0 : ℂ)).im = 0 := by
  have h1 := real_expansion hreal hev
  have h2 : ∀ᶠ x : ℝ in 𝓝[≠] x0, (h (x : ℂ)).im = 0 := by
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with x hx hne
    have : (x - x0) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hne)
    exact (mul_eq_zero.1 hx.2).resolve_left this
  have h3 : Tendsto (fun x : ℝ => (h (x : ℂ)).im) (𝓝[≠] x0) (𝓝 (h (x0 : ℂ)).im) := by
    have := (Complex.continuous_im.continuousAt.tendsto.comp
      (hh.tendsto.comp (Complex.continuous_ofReal.tendsto x0)))
    exact this.mono_left nhdsWithin_le_nhds
  have h4 : Tendsto (fun x : ℝ => (h (x : ℂ)).im) (𝓝[≠] x0) (𝓝 0) :=
    tendsto_const_nhds.congr' (h2.mono fun x hx => hx.symm)
  exact tendsto_nhds_unique h3 h4

/-- A pure inequality: `q` with `Im q ≥ L/4`, `Re (q²) > 0` has `|Im (q²)| ≥ L²/8`. -/
theorem sq_contradiction {q : ℂ} {L : ℝ} (hL : 0 < L) (hq : L / 4 ≤ q.im) (hre : 0 < (q ^ 2).re) :
    L ^ 2 / 8 ≤ |(q ^ 2).im| := by
  have h1 : (q ^ 2).re = q.re ^ 2 - q.im ^ 2 := by simp [pow_two, Complex.mul_re]
  have h2 : (q ^ 2).im = 2 * q.re * q.im := by simp [pow_two, Complex.mul_im]; ring
  rw [h1] at hre
  rw [h2]
  have hβ : 0 < q.im := lt_of_lt_of_le (by positivity) hq
  have hα : q.im < |q.re| := by
    have : q.im ^ 2 < |q.re| ^ 2 := by rw [sq_abs]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) this
  rw [abs_mul, abs_mul, abs_of_pos hβ, abs_two]
  nlinarith [abs_nonneg q.re]

theorem double_strict (hΔ : Differentiable ℂ Δ) (hreal : ∀ x : ℝ, (Δ (x : ℂ)).im = 0)
    (hσ : σ = 1 ∨ σ = -1) (hL : 0 < L) (hray : Ray Δ L σ x0) (hx0 : Δ (x0 : ℂ) = 2 * (σ : ℂ))
    (h2 : analyticOrderAt (fun z => Δ z - 2 * (σ : ℂ)) (x0 : ℂ) = 2) :
    ∀ᶠ x : ℝ in 𝓝[≠] x0, |(Δ (x : ℂ)).re| < 2 := by
  obtain ⟨h, hh_an, hh_ne, hh_ev⟩ := ((analytic_f hΔ (x0 : ℂ)).analyticOrderAt_eq_natCast (n := 2)).1 h2
  have him := im_h_zero hreal hh_an.continuousAt hh_ev
  set c : ℝ := (h (x0 : ℂ)).re with hc
  have hhc : h (x0 : ℂ) = (c : ℂ) := Complex.ext (by simp [hc]) (by simp [him])
  have hc0 : c ≠ 0 := by
    intro h0; apply hh_ne; rw [hhc, h0]; simp
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> simp [h]
  have hσsq : σ ^ 2 = 1 := by rcases hσ with h | h <;> simp [h]
  -- the sign of `σ c`
  have hm : σ * c < 0 := by
    by_contra hnot
    push Not at hnot
    have hmpos : 0 < σ * c := lt_of_le_of_ne hnot (Ne.symm (mul_ne_zero hσ0 hc0))
    obtain ⟨w, hw0, hwim, hwΔ⟩ := hray
    have hrel : ∀ᶠ y : ℝ in 𝓝[>] 0, 4 * Complex.sin (w y) ^ 2 =
        (σ : ℂ) * (y : ℂ) ^ 2 * h ((x0 : ℂ) + (y : ℂ) * Complex.I) := by
      filter_upwards [(ray_tendsto x0).eventually hh_ev, self_mem_nhdsWithin] with y hy hypos
      have e1 := hwΔ y hypos
      rw [hy, smul_eq_mul] at e1
      have hr : ((x0 : ℂ) + (y : ℂ) * Complex.I) - (x0 : ℂ) = (y : ℂ) * Complex.I := by ring
      rw [hr] at e1
      have hσc : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσsq
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination (σ : ℂ) * e1 - 4 * Complex.sin (w y) ^ 2 * hσc -
        (σ : ℂ) * (y : ℂ) ^ 2 * h ((x0 : ℂ) + (y : ℂ) * Complex.I) * hI
    -- `sin w / w → 1`
    have hwne : ∀ᶠ y : ℝ in 𝓝[>] 0, w y ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with y hy h0
      have := hwim y hy
      rw [h0] at this
      simp at this
      have : 0 < L * y / 4 := by have : (0 : ℝ) < y := hy; positivity
      linarith
    have hw0' : Tendsto w (𝓝[>] 0) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hw0, hwne⟩
    have hsinc : Tendsto (fun y : ℝ => Complex.sin (w y) / w y) (𝓝[>] 0) (𝓝 1) := by
      have hd := (Complex.hasDerivAt_sin (0 : ℂ)).tendsto_slope
      simp only [Complex.cos_zero] at hd
      have := hd.comp hw0'
      refine this.congr' ?_
      filter_upwards with y
      simp [Function.comp_def, slope_def_field]
    have hhcont : Tendsto (fun y : ℝ => h ((x0 : ℂ) + (y : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 (c : ℂ)) := by
      rw [← hhc]
      exact hh_an.continuousAt.tendsto.comp (ray_tendsto x0)
    -- q = w / y ; q² → σ c / 4
    set q : ℝ → ℂ := fun y => w y / (y : ℂ) with hq
    have hQ : Tendsto (fun y : ℝ => q y ^ 2) (𝓝[>] 0) (𝓝 ((σ * c : ℝ) / 4 : ℂ)) := by
      have h1 : Tendsto (fun y : ℝ => ((σ : ℂ) * h ((x0 : ℂ) + (y : ℂ) * Complex.I) / 4) /
          (Complex.sin (w y) / w y) ^ 2) (𝓝[>] 0) (𝓝 (((σ : ℂ) * (c : ℂ) / 4) / (1 : ℂ) ^ 2)) := by
        refine Tendsto.div ((tendsto_const_nhds.mul hhcont).div_const 4) (hsinc.pow 2) (by simp)
      have e : ((σ : ℂ) * (c : ℂ) / 4) / (1 : ℂ) ^ 2 = ((σ * c : ℝ) / 4 : ℂ) := by push_cast; ring
      rw [e] at h1
      refine h1.congr' ?_
      filter_upwards [hrel, hwne, self_mem_nhdsWithin, hsinc.eventually (isOpen_ne.mem_nhds (one_ne_zero))]
        with y hy hw hypos hs
      have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hypos)
      have hs0 : Complex.sin (w y) / w y ≠ 0 := hs
      have hw0y : w y ≠ 0 := hw
      rw [div_eq_iff (pow_ne_zero 2 hs0)]
      have e2 : q y ^ 2 * (Complex.sin (w y) / w y) ^ 2 = Complex.sin (w y) ^ 2 / (y : ℂ) ^ 2 := by
        simp only [hq]
        field_simp
      rw [e2, eq_div_iff (pow_ne_zero 2 hy0)]
      linear_combination (-(1 : ℂ) / 4) * hy
    have hReQ := (Complex.continuous_re.tendsto _).comp hQ
    have hImQ := (Complex.continuous_im.tendsto _).comp hQ
    have hv1 : ∀ᶠ y : ℝ in 𝓝[>] 0, 0 < (q y ^ 2).re := by
      have : (((σ * c : ℝ) / 4 : ℂ)).re = σ * c / 4 := by simp
      have h' := hReQ
      simp only [Function.comp_def, this] at h'
      exact h'.eventually (lt_mem_nhds (by positivity))
    have hv2 : ∀ᶠ y : ℝ in 𝓝[>] 0, |(q y ^ 2).im| < L ^ 2 / 8 := by
      have : (((σ * c : ℝ) / 4 : ℂ)).im = 0 := by simp
      have h' := hImQ
      simp only [Function.comp_def, this] at h'
      have := h'.abs
      simp only [abs_zero] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    have E1 : ∀ᶠ y : ℝ in 𝓝[>] 0, 0 < y := eventually_mem_nhdsWithin
    obtain ⟨y, hy1, hy2, hy3⟩ := (E1.and (hv1.and hv2)).exists
    have hypos : 0 < y := hy1
    have hqim : L / 4 ≤ (q y).im := by
      simp only [hq, Complex.div_ofReal_im]
      rw [le_div_iff₀ hypos]
      have := hwim y hypos
      linarith
    have := sq_contradiction hL hqim hy2
    linarith [hy3, this]
  -- strict bands
  have hev1 : ∀ᶠ x : ℝ in 𝓝 x0, σ * (h (x : ℂ)).re < 0 := by
    have : Tendsto (fun x : ℝ => σ * (h (x : ℂ)).re) (𝓝 x0) (𝓝 (σ * c)) :=
      tendsto_const_nhds.mul ((Complex.continuous_re.tendsto _).comp
        (hh_an.continuousAt.tendsto.comp (Complex.continuous_ofReal.tendsto x0)))
    exact this.eventually (gt_mem_nhds hm)
  have hev2 : ∀ᶠ x : ℝ in 𝓝 x0, |(Δ (x : ℂ)).re - 2 * σ| < 1 := by
    have hcont : Continuous fun x : ℝ => (Δ (x : ℂ)).re :=
      Complex.continuous_re.comp (hΔ.continuous.comp Complex.continuous_ofReal)
    have hv : (Δ (x0 : ℂ)).re = 2 * σ := by rw [hx0]; simp
    have := (hcont.tendsto x0)
    rw [hv] at this
    exact (this.sub_const (2 * σ)).abs.eventually (by simpa using gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hev3 := real_expansion hreal hh_ev
  filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, nhdsWithin_le_nhds hev3,
    self_mem_nhdsWithin] with x h1 h2' h3 hne
  have hx2 : 0 < (x - x0) ^ 2 := by
    have := sub_ne_zero.2 hne
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 this))
  have key : σ * (Δ (x : ℂ)).re < 2 := by
    have : σ * ((Δ (x : ℂ)).re - 2 * σ) < 0 := by
      rw [h3.1]
      have := mul_neg_of_pos_of_neg hx2 h1
      nlinarith [this]
    nlinarith [hσsq]
  have key2 : 1 < σ * (Δ (x : ℂ)).re := by
    have := abs_lt.1 h2'
    rcases hσ with h | h
    · rw [h]; linarith [this.1]
    · rw [h]; linarith [this.2]
  rw [abs_lt]
  rcases hσ with h | h
  · rw [h] at key key2; constructor <;> linarith
  · rw [h] at key key2; constructor <;> linarith

theorem simple_sides (hΔ : Differentiable ℂ Δ) (hreal : ∀ x : ℝ, (Δ (x : ℂ)).im = 0)
    (hσ : σ = 1 ∨ σ = -1) (hx0 : Δ (x0 : ℂ) = 2 * (σ : ℂ))
    (h1 : analyticOrderAt (fun z => Δ z - 2 * (σ : ℂ)) (x0 : ℂ) = 1) :
    ((∀ᶠ x : ℝ in 𝓝[>] x0, 2 < |(Δ (x : ℂ)).re|) ∧ (∀ᶠ x : ℝ in 𝓝[<] x0, |(Δ (x : ℂ)).re| < 2)) ∨
    ((∀ᶠ x : ℝ in 𝓝[<] x0, 2 < |(Δ (x : ℂ)).re|) ∧ (∀ᶠ x : ℝ in 𝓝[>] x0, |(Δ (x : ℂ)).re| < 2)) := by
  obtain ⟨h, hh_an, hh_ne, hh_ev⟩ := ((analytic_f hΔ (x0 : ℂ)).analyticOrderAt_eq_natCast (n := 1)).1 h1
  have him := im_h_zero hreal hh_an.continuousAt hh_ev
  set c : ℝ := (h (x0 : ℂ)).re with hc
  have hhc : h (x0 : ℂ) = (c : ℂ) := Complex.ext (by simp [hc]) (by simp [him])
  have hc0 : c ≠ 0 := by
    intro h0; apply hh_ne; rw [hhc, h0]; simp
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> simp [h]
  have hσsq : σ ^ 2 = 1 := by rcases hσ with h | h <;> simp [h]
  have hm0 : σ * c ≠ 0 := mul_ne_zero hσ0 hc0
  have hcont_h : Tendsto (fun x : ℝ => σ * (h (x : ℂ)).re) (𝓝 x0) (𝓝 (σ * c)) :=
    tendsto_const_nhds.mul ((Complex.continuous_re.tendsto _).comp
      (hh_an.continuousAt.tendsto.comp (Complex.continuous_ofReal.tendsto x0)))
  have hev2 : ∀ᶠ x : ℝ in 𝓝 x0, |(Δ (x : ℂ)).re - 2 * σ| < 1 := by
    have hcont : Continuous fun x : ℝ => (Δ (x : ℂ)).re :=
      Complex.continuous_re.comp (hΔ.continuous.comp Complex.continuous_ofReal)
    have hv : (Δ (x0 : ℂ)).re = 2 * σ := by rw [hx0]; simp
    have := (hcont.tendsto x0)
    rw [hv] at this
    exact (this.sub_const (2 * σ)).abs.eventually (by simpa using gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hev3 := real_expansion hreal hh_ev
  -- common facts for real x near x0
  have core : ∀ x : ℝ, |(Δ (x : ℂ)).re - 2 * σ| < 1 → (Δ (x : ℂ)).re - 2 * σ = (x - x0) ^ 1 * (h (x : ℂ)).re →
      1 < σ * (Δ (x : ℂ)).re ∧ σ * (Δ (x : ℂ)).re - 2 = (x - x0) * (σ * (h (x : ℂ)).re) := by
    intro x h2 h3
    constructor
    · have := abs_lt.1 h2
      rcases hσ with h | h
      · rw [h]; linarith [this.1]
      · rw [h]; linarith [this.2]
    · have : σ * (Δ (x : ℂ)).re - 2 = σ * ((Δ (x : ℂ)).re - 2 * σ) := by nlinarith [hσsq]
      rw [this, h3]; ring
  have abs_lt2 : ∀ x : ℝ, 1 < σ * (Δ (x : ℂ)).re → σ * (Δ (x : ℂ)).re < 2 → |(Δ (x : ℂ)).re| < 2 := by
    intro x a b
    rw [abs_lt]
    rcases hσ with h | h
    · rw [h] at a b; constructor <;> linarith
    · rw [h] at a b; constructor <;> linarith
  have abs_gt2 : ∀ x : ℝ, 2 < σ * (Δ (x : ℂ)).re → 2 < |(Δ (x : ℂ)).re| := by
    intro x a
    rcases hσ with h | h
    · rw [h] at a; exact lt_of_lt_of_le (by linarith) (le_abs_self _)
    · rw [h] at a; exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
  rcases lt_or_gt_of_ne hm0 with hneg | hpos
  · -- σ c < 0 : right side is a band, left side is a gap
    right
    have hev1 : ∀ᶠ x : ℝ in 𝓝 x0, σ * (h (x : ℂ)).re < 0 := hcont_h.eventually (gt_mem_nhds hneg)
    constructor
    · filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, nhdsWithin_le_nhds hev3,
        self_mem_nhdsWithin (s := Iio x0)] with x a b d hx
      have hxlt : x - x0 < 0 := sub_neg.2 hx
      obtain ⟨k1, k2⟩ := core x b d.1
      apply abs_gt2
      have : 0 < (x - x0) * (σ * (h (x : ℂ)).re) := mul_pos_of_neg_of_neg hxlt a
      linarith
    · filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, nhdsWithin_le_nhds hev3,
        self_mem_nhdsWithin (s := Ioi x0)] with x a b d hx
      have hxgt : 0 < x - x0 := sub_pos.2 hx
      obtain ⟨k1, k2⟩ := core x b d.1
      apply abs_lt2 x k1
      have : (x - x0) * (σ * (h (x : ℂ)).re) < 0 := mul_neg_of_pos_of_neg hxgt a
      linarith
  · left
    have hev1 : ∀ᶠ x : ℝ in 𝓝 x0, 0 < σ * (h (x : ℂ)).re := hcont_h.eventually (lt_mem_nhds hpos)
    constructor
    · filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, nhdsWithin_le_nhds hev3,
        self_mem_nhdsWithin (s := Ioi x0)] with x a b d hx
      have hxgt : 0 < x - x0 := sub_pos.2 hx
      obtain ⟨k1, k2⟩ := core x b d.1
      apply abs_gt2
      have : 0 < (x - x0) * (σ * (h (x : ℂ)).re) := mul_pos hxgt a
      linarith
    · filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, nhdsWithin_le_nhds hev3,
        self_mem_nhdsWithin (s := Iio x0)] with x a b d hx
      have hxlt : x - x0 < 0 := sub_neg.2 hx
      obtain ⟨k1, k2⟩ := core x b d.1
      apply abs_lt2 x k1
      have : (x - x0) * (σ * (h (x : ℂ)).re) < 0 := mul_neg_of_neg_of_pos hxlt a
      linarith

end Local

end QuantumNLS.RootGapLocal

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RootGapLocal.zeros_real
#print axioms QuantumNLS.RootGapLocal.lower_bound
#print axioms QuantumNLS.RootGapLocal.order_cases
#print axioms QuantumNLS.RootGapLocal.double_strict
#print axioms QuantumNLS.RootGapLocal.simple_sides
