import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB2CutoffDense

/-! # Track B, step B2: Fourier-side bound for the fixed-cutoff Duhamel operator

For a time-side Schwartz cutoff `η` with `Ψ = 𝓕⁻ η` and a forcing profile with inverse transform
`θ`, the fixed-cutoff Duhamel output `η(t) ∫₀ᵗ e^{-iλ(t-r)} g(r) dr` has inverse transform
`∫ θ(ζ) K(ξ - λ/2π, ζ - λ/2π) dζ` with the kernel (in Mathlib's frequency variable)
`K(x, z) = (Ψ(x) - Ψ(x - z)) / (2πiz)` (`duhKer`). This file proves the scalar estimate
behind Pro's (eq:duhamel): for `1/2 < c ≤ 1`,
`∫ ⟨2πx⟩^{2c} (∫ |K(x,z)| |θ(z)| dz)² dx ≤ C ∫ ⟨2πz⟩^{2(c-1)} |θ(z)|² dz`
(`duhamel_kernel_bound`), uniformly in `θ`, following Pro's split:
* `|z| ≤ 1` (Taylor part): mean value theorem, `|K(x,z)| ≤ A ⟨2πx⟩^{-2}`;
* `|z| > 1`: `|K(x,z)| ≤ (|Ψ(x)| + |Ψ(x-z)|)/(2π|z|)`; the `Ψ(x)` term (constant-in-time part) by
  Cauchy–Schwarz with `∫_{|z|>1} |z|^{-2}⟨z⟩^{2(1-c)} < ∞` (`c > 1/2`); the `Ψ(x-z)` term
  (oscillatory part) by Peetre's inequality and Young/Schur with the kernel `|Ψ|⟨2π·⟩^c ∈ L¹`.
All integrals are in `ℝ≥0∞`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory SchwartzMap
open scoped ENNReal

theorem enn_mul_le_left {a b : ℝ≥0∞} (h : a ≤ b) (c : ℝ≥0∞) : c * a ≤ c * b :=
  mul_le_mul_of_nonneg_left h zero_le

theorem enn_mul_le_right {a b : ℝ≥0∞} (h : a ≤ b) (c : ℝ≥0∞) : a * c ≤ b * c :=
  mul_le_mul_of_nonneg_right h zero_le

/-- The time-frequency weight `⟨2πx⟩^e`, in Mathlib's frequency variable. -/
def bw (e x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (brk (2 * Real.pi * x) ^ e)

theorem measurable_bw (e : ℝ) : Measurable (bw e) :=
  ENNReal.measurable_ofReal.comp
    ((continuous_brk.comp (continuous_const.mul continuous_id)).measurable.pow_const e)

theorem bw_mul (e e' x : ℝ) : bw e x * bw e' x = bw (e + e') x := by
  unfold bw
  rw [← ENNReal.ofReal_mul (brk_rpow_nonneg _ _), ← Real.rpow_add (brk_pos _)]

theorem bw_zero (x : ℝ) : bw 0 x = 1 := by simp [bw]

theorem bw_sq (e x : ℝ) : bw e x ^ 2 = bw (2 * e) x := by
  rw [sq, bw_mul, two_mul]

theorem bw_mono {e e' : ℝ} (h : e ≤ e') (x : ℝ) : bw e x ≤ bw e' x :=
  ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (one_le_brk _) h)

theorem lintegral_bw_lt_top {q : ℝ} (hq : 1 < q) : ∫⁻ x, bw (-q) x < ⊤ :=
  ((integrable_brk_rpow hq).comp_mul_left' (by positivity : (2 * Real.pi) ≠ 0)).lintegral_lt_top

theorem brk_rpow_neg_two (r : ℝ) : brk r ^ (-2 : ℝ) = 1 / brk r ^ 2 := by
  rw [Real.rpow_neg (brk_pos r).le, Real.rpow_two, one_div]

/-- A Schwartz decay constant: `⟨2πy⟩² |f(y)| ≤ decayC f`. -/
def decayC (f : 𝓢(ℝ, ℂ)) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 f + 4 * Real.pi ^ 2 * SchwartzMap.seminorm ℝ 2 0 f

theorem decayC_nonneg (f : 𝓢(ℝ, ℂ)) : 0 ≤ decayC f :=
  add_nonneg (apply_nonneg _ _) (mul_nonneg (by positivity) (apply_nonneg _ _))

theorem norm_le_decayC (f : 𝓢(ℝ, ℂ)) (y : ℝ) :
    ‖f y‖ ≤ decayC f / brk (2 * Real.pi * y) ^ 2 := by
  have a := SchwartzMap.norm_le_seminorm ℝ f y
  have b := SchwartzMap.norm_pow_mul_le_seminorm ℝ f 2 y
  rw [Real.norm_eq_abs, sq_abs] at b
  have c := mul_le_mul_of_nonneg_left b (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2)
  rw [le_div_iff₀ (pow_pos (brk_pos _) 2), brk_sq]
  unfold decayC
  nlinarith [c, a]

theorem enorm_le_decayC (f : 𝓢(ℝ, ℂ)) (y : ℝ) :
    ‖f y‖ₑ ≤ ENNReal.ofReal (decayC f) * bw (-2) y := by
  rw [← ofReal_norm, bw, brk_rpow_neg_two, ← ENNReal.ofReal_mul (decayC_nonneg f),
    ← div_eq_mul_one_div]
  exact ENNReal.ofReal_le_ofReal (norm_le_decayC f y)

/-- The fixed-cutoff Duhamel kernel `K(x,z) = (Ψ(x) - Ψ(x-z))/(2πiz)` (value `0` at `z = 0`). -/
def duhKer (Ψ : ℝ → ℂ) (x z : ℝ) : ℂ := (Ψ x - Ψ (x - z)) / (2 * Real.pi * Complex.I * z)

theorem norm_duhDen (z : ℝ) : ‖(2 * Real.pi * Complex.I * z : ℂ)‖ = 2 * Real.pi * |z| := by
  simp [abs_of_pos Real.pi_pos]

theorem brk_le_of_abs_sub_le {x y : ℝ} (h : |x - y| ≤ 1) :
    brk (2 * Real.pi * x) ≤ (1 + 2 * Real.pi) * brk (2 * Real.pi * y) := by
  have h1 := brk_add_le (2 * Real.pi * y) (2 * Real.pi * (x - y))
  rw [show 2 * Real.pi * y + 2 * Real.pi * (x - y) = 2 * Real.pi * x by ring] at h1
  have h2 : |2 * Real.pi * (x - y)| ≤ 2 * Real.pi := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact mul_le_of_le_one_right (by positivity) h
  have h4 : 2 * Real.pi ≤ 2 * Real.pi * brk (2 * Real.pi * y) :=
    le_mul_of_one_le_right (by positivity) (one_le_brk _)
  linarith

/-- The constant of the low-frequency (Taylor) kernel bound. -/
def duhA (Ψ : 𝓢(ℝ, ℂ)) : ℝ :=
  (1 + 2 * Real.pi) ^ 2 * decayC (SchwartzMap.derivCLM ℝ ℂ Ψ) / (2 * Real.pi)

theorem duhA_nonneg (Ψ : 𝓢(ℝ, ℂ)) : 0 ≤ duhA Ψ := by
  unfold duhA
  have := decayC_nonneg (SchwartzMap.derivCLM ℝ ℂ Ψ)
  positivity

/-- Taylor part: for `|z| ≤ 1`, `|K(x,z)| ≤ A / ⟨2πx⟩²`. -/
theorem norm_duhKer_le_low (Ψ : 𝓢(ℝ, ℂ)) (x : ℝ) {z : ℝ} (hz : |z| ≤ 1) :
    ‖duhKer Ψ x z‖ ≤ duhA Ψ / brk (2 * Real.pi * x) ^ 2 := by
  have hA := duhA_nonneg Ψ
  have hbx := brk_pos (2 * Real.pi * x)
  rcases eq_or_ne z 0 with rfl | hz0
  · have : duhKer Ψ x 0 = 0 := by simp [duhKer]
    rw [this, norm_zero]
    positivity
  set D := decayC (SchwartzMap.derivCLM ℝ ℂ Ψ) with hD
  have hD0 : 0 ≤ D := decayC_nonneg _
  set M := (1 + 2 * Real.pi) ^ 2 * D / brk (2 * Real.pi * x) ^ 2 with hM
  have hbound : ∀ y ∈ Set.Icc (x - 1) (x + 1), ‖deriv (⇑Ψ) y‖ ≤ M := by
    intro y hy
    have hxy : |x - y| ≤ 1 := abs_le.2 ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hd := norm_le_decayC (SchwartzMap.derivCLM ℝ ℂ Ψ) y
    rw [SchwartzMap.derivCLM_apply] at hd
    have hb := brk_le_of_abs_sub_le hxy
    have hsq : brk (2 * Real.pi * x) ^ 2 ≤ ((1 + 2 * Real.pi) * brk (2 * Real.pi * y)) ^ 2 :=
      pow_le_pow_left₀ hbx.le hb 2
    calc ‖deriv (⇑Ψ) y‖ ≤ D / brk (2 * Real.pi * y) ^ 2 := hd
      _ = (1 + 2 * Real.pi) ^ 2 * D / ((1 + 2 * Real.pi) * brk (2 * Real.pi * y)) ^ 2 := by
          rw [mul_pow, mul_div_mul_left _ _ (by positivity : ((1 : ℝ) + 2 * Real.pi) ^ 2 ≠ 0)]
      _ ≤ M := by
          rw [hM]
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
  have hmem1 : x - z ∈ Set.Icc (x - 1) (x + 1) := by
    have := abs_le.1 hz
    constructor <;> linarith [this.1, this.2]
  have hmem2 : x ∈ Set.Icc (x - 1) (x + 1) := ⟨by linarith, by linarith⟩
  have hmvt := (convex_Icc (x - 1) (x + 1)).norm_image_sub_le_of_norm_deriv_le
    (fun y _ => Ψ.differentiableAt) hbound hmem1 hmem2
  rw [show x - (x - z) = z by ring, Real.norm_eq_abs] at hmvt
  have hzpos : 0 < 2 * Real.pi * |z| := mul_pos (by positivity) (abs_pos.2 hz0)
  unfold duhKer
  rw [norm_div, norm_duhDen, div_le_iff₀ hzpos]
  calc ‖Ψ x - Ψ (x - z)‖ ≤ M * |z| := hmvt
    _ = duhA Ψ / brk (2 * Real.pi * x) ^ 2 * (2 * Real.pi * |z|) := by
        rw [hM, duhA, ← hD]
        field_simp

/-- High part: `|K(x,z)| ≤ (|Ψ(x)| + |Ψ(x-z)|)/(2π|z|)`. -/
theorem norm_duhKer_le_high (Ψ : ℝ → ℂ) (x z : ℝ) :
    ‖duhKer Ψ x z‖ ≤ (‖Ψ x‖ + ‖Ψ (x - z)‖) * (1 / (2 * Real.pi * |z|)) := by
  unfold duhKer
  rw [norm_div, norm_duhDen, ← div_eq_mul_one_div]
  gcongr
  exact norm_sub_le _ _

/-- The low-frequency set `{|z| ≤ 1}`. -/
def lowSet : Set ℝ := {z | |z| ≤ 1}

theorem measurableSet_lowSet : MeasurableSet lowSet :=
  measurableSet_le continuous_abs.measurable measurable_const

theorem lowSet_eq : lowSet = Set.Icc (-1) 1 :=
  Set.ext fun z => by show |z| ≤ 1 ↔ -1 ≤ z ∧ z ≤ 1; exact abs_le

/-- `1/(2π|z|)` in `ℝ≥0∞`. -/
def invq (z : ℝ) : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * Real.pi * |z|))

theorem measurable_invq : Measurable invq :=
  ENNReal.measurable_ofReal.comp
    (measurable_const.div (measurable_const.mul continuous_abs.measurable))

/-- The high-frequency forcing weight `1_{|z|>1} |θ(z)| / (2π|z|)`. -/
def hiW (T : ℝ → ℝ≥0∞) (z : ℝ) : ℝ≥0∞ := lowSetᶜ.indicator 1 z * invq z * T z

theorem measurable_hiW {T : ℝ → ℝ≥0∞} (hT : Measurable T) : Measurable (hiW T) :=
  ((measurable_one.indicator measurableSet_lowSet.compl).mul measurable_invq).mul hT

theorem indicator_one_sq (s : Set ℝ) (z : ℝ) :
    s.indicator (1 : ℝ → ℝ≥0∞) z ^ 2 = s.indicator 1 z := by
  by_cases h : z ∈ s <;> simp [h]

theorem enorm_duhKer_le (Ψ : 𝓢(ℝ, ℂ)) (x z : ℝ) :
    ‖duhKer Ψ x z‖ₑ ≤ lowSet.indicator 1 z * (ENNReal.ofReal (duhA Ψ) * bw (-2) x) +
      lowSetᶜ.indicator 1 z * ((‖Ψ x‖ₑ + ‖Ψ (x - z)‖ₑ) * invq z) := by
  by_cases hz : z ∈ lowSet
  · have hz' : z ∉ lowSetᶜ := fun h => h hz
    rw [Set.indicator_of_mem hz, Set.indicator_of_notMem hz', Pi.one_apply, one_mul, zero_mul,
      add_zero]
    rw [← ofReal_norm, bw, brk_rpow_neg_two, ← ENNReal.ofReal_mul (duhA_nonneg Ψ),
      ← div_eq_mul_one_div]
    exact ENNReal.ofReal_le_ofReal (norm_duhKer_le_low Ψ x hz)
  · have hz' : z ∈ lowSetᶜ := hz
    rw [Set.indicator_of_notMem hz, Set.indicator_of_mem hz', Pi.one_apply, one_mul, zero_mul,
      zero_add]
    rw [invq, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (norm_duhKer_le_high Ψ x z)

/-- Splitting the kernel integral into the Taylor, constant-in-time and oscillatory parts. -/
theorem lintegral_duhKer_le (Ψ : 𝓢(ℝ, ℂ)) (T : ℝ → ℝ≥0∞) (hT : Measurable T) (x : ℝ) :
    ∫⁻ z, ‖duhKer Ψ x z‖ₑ * T z ≤
      ENNReal.ofReal (duhA Ψ) * bw (-2) x * (∫⁻ z, lowSet.indicator 1 z * T z) +
      ‖Ψ x‖ₑ * (∫⁻ z, hiW T z) + ∫⁻ z, ‖Ψ (x - z)‖ₑ * hiW T z := by
  have hl : Measurable fun z => lowSet.indicator (1 : ℝ → ℝ≥0∞) z * T z :=
    (measurable_one.indicator measurableSet_lowSet).mul hT
  have hh := measurable_hiW hT
  calc ∫⁻ z, ‖duhKer Ψ x z‖ₑ * T z
      ≤ ∫⁻ z, (ENNReal.ofReal (duhA Ψ) * bw (-2) x * (lowSet.indicator 1 z * T z) +
          ‖Ψ x‖ₑ * hiW T z) + ‖Ψ (x - z)‖ₑ * hiW T z := by
        refine lintegral_mono fun z => ?_
        calc ‖duhKer Ψ x z‖ₑ * T z ≤ (lowSet.indicator 1 z * (ENNReal.ofReal (duhA Ψ) * bw (-2) x) +
              lowSetᶜ.indicator 1 z * ((‖Ψ x‖ₑ + ‖Ψ (x - z)‖ₑ) * invq z)) * T z :=
              enn_mul_le_right (enorm_duhKer_le Ψ x z) _
          _ = _ := by unfold hiW; ring
    _ = _ := by
        have hm1 : Measurable fun z => ENNReal.ofReal (duhA Ψ) * bw (-2) x *
            (lowSet.indicator 1 z * T z) + ‖Ψ x‖ₑ * hiW T z := (hl.const_mul _).add (hh.const_mul _)
        have hm2 : Measurable fun z => ENNReal.ofReal (duhA Ψ) * bw (-2) x *
            (lowSet.indicator 1 z * T z) := hl.const_mul _
        rw [lintegral_add_left hm1, lintegral_add_left hm2, lintegral_const_mul _ hl,
          lintegral_const_mul _ hh]

/-- Cauchy–Schwarz in `ℝ≥0∞`. -/
theorem sq_lintegral_mul_le (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ z, f z * g z) ^ 2 ≤ (∫⁻ z, f z ^ 2) * ∫⁻ z, g z ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hf.aemeasurable hg.aemeasurable
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ z, f z * g z) ^ 2
      ≤ ((∫⁻ z, f z ^ 2) ^ (1 / (2 : ℝ)) * (∫⁻ z, g z ^ 2) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ bot_le h 2
    _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

theorem add_sq_le_two_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h
  simpa only [ENNReal.rpow_two] using h

theorem add3_sq_le (u v w : ℝ≥0∞) : (u + v + w) ^ 2 ≤ 4 * (u ^ 2 + v ^ 2 + w ^ 2) := by
  calc (u + v + w) ^ 2 ≤ 2 * ((u + v) ^ 2 + w ^ 2) := add_sq_le_two_mul _ _
    _ ≤ 2 * (2 * (u ^ 2 + v ^ 2) + w ^ 2) := by gcongr; exact add_sq_le_two_mul _ _
    _ ≤ 2 * (2 * (u ^ 2 + v ^ 2) + 2 * w ^ 2) := by
        gcongr
        exact le_mul_of_one_le_left zero_le (by norm_num)
    _ = 4 * (u ^ 2 + v ^ 2 + w ^ 2) := by ring

theorem one_le_bw_low {c : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c ≤ 1) {z : ℝ} (hz : |z| ≤ 1) :
    1 ≤ ENNReal.ofReal (1 + 2 * Real.pi) * bw (2 * (c - 1)) z := by
  rw [bw, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  have hb : brk (2 * Real.pi * z) ≤ 1 + 2 * Real.pi := by
    have h1 := brk_le_one_add_abs (2 * Real.pi * z)
    have h2 : |2 * Real.pi * z| ≤ 2 * Real.pi := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      exact mul_le_of_le_one_right (by positivity) hz
    linarith
  have h3 : (1 + 2 * Real.pi) ^ (2 * (c - 1)) ≤ brk (2 * Real.pi * z) ^ (2 * (c - 1)) :=
    Real.rpow_le_rpow_of_nonpos (brk_pos _) hb (by linarith)
  have h4 : (1 + 2 * Real.pi) ^ (-1 : ℝ) ≤ (1 + 2 * Real.pi) ^ (2 * (c - 1)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_pos]) (by linarith)
  have h5 : (1 + 2 * Real.pi) * (1 + 2 * Real.pi) ^ (-1 : ℝ) = 1 := by
    rw [Real.rpow_neg_one, mul_inv_cancel₀ (by positivity)]
  calc (1 : ℝ) = (1 + 2 * Real.pi) * (1 + 2 * Real.pi) ^ (-1 : ℝ) := h5.symm
    _ ≤ (1 + 2 * Real.pi) * brk (2 * Real.pi * z) ^ (2 * (c - 1)) :=
      mul_le_mul_of_nonneg_left (h4.trans h3) (by positivity)

/-- Taylor part: `(∫_{|z|≤1} |θ|)² ≤ 2(1+2π) ∫ ⟨2πz⟩^{2(c-1)} |θ|²`. -/
theorem sq_lintegral_low_le {c : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c ≤ 1) (T : ℝ → ℝ≥0∞)
    (hT : Measurable T) :
    (∫⁻ z, lowSet.indicator 1 z * T z) ^ 2 ≤
      ENNReal.ofReal 2 * (ENNReal.ofReal (1 + 2 * Real.pi) *
        ∫⁻ z, bw (2 * (c - 1)) z * T z ^ 2) := by
  have hχ : Measurable (lowSet.indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_one.indicator measurableSet_lowSet
  have e : ∀ z, lowSet.indicator (1 : ℝ → ℝ≥0∞) z * T z =
      lowSet.indicator 1 z * (lowSet.indicator 1 z * T z) := fun z => by
    by_cases h : z ∈ lowSet <;> simp [h]
  have hg : Measurable fun z => lowSet.indicator (1 : ℝ → ℝ≥0∞) z * T z := hχ.mul hT
  rw [lintegral_congr e]
  refine (sq_lintegral_mul_le _ _ hχ hg).trans ?_
  have h1 : ∫⁻ z, lowSet.indicator (1 : ℝ → ℝ≥0∞) z ^ 2 = ENNReal.ofReal 2 := by
    simp_rw [indicator_one_sq]
    rw [lintegral_indicator_one measurableSet_lowSet, lowSet_eq, Real.volume_Icc]
    norm_num
  rw [h1]
  refine enn_mul_le_left ?_ _
  have hm : Measurable fun z => bw (2 * (c - 1)) z * T z ^ 2 := (measurable_bw _).mul (hT.pow_const 2)
  rw [← lintegral_const_mul _ hm]
  refine lintegral_mono fun z => ?_
  rw [mul_pow, indicator_one_sq]
  by_cases h : z ∈ lowSet
  · rw [Set.indicator_of_mem h, Pi.one_apply, one_mul]
    calc T z ^ 2 = 1 * T z ^ 2 := (one_mul _).symm
      _ ≤ ENNReal.ofReal (1 + 2 * Real.pi) * bw (2 * (c - 1)) z * T z ^ 2 := by
          gcongr
          exact one_le_bw_low hc hc1 h
      _ = _ := by ring
  · simp [h]

theorem invq_sq_le_high {z : ℝ} (hz : z ∉ lowSet) :
    invq z ^ 2 ≤ ENNReal.ofReal 2 * bw (-2) z := by
  have h0 : ¬ |z| ≤ 1 := hz
  have hz1 : 1 < |z| := not_le.1 h0
  have ha1 : 1 ≤ 2 * Real.pi * |z| := by nlinarith [Real.pi_gt_three]
  have hb : brk (2 * Real.pi * z) ^ 2 = 1 + (2 * Real.pi * |z|) ^ 2 := by
    rw [brk_sq, mul_pow, mul_pow (2 * Real.pi) |z|, sq_abs]
  rw [invq, bw, brk_rpow_neg_two, hb, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_pow, one_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Constant-in-time part: `(∫_{|z|>1} |θ|/(2π|z|))² ≤ 2 ∫⟨2πz⟩^{-2c} · ∫ ⟨2πz⟩^{2(c-1)} |θ|²`. -/
theorem sq_lintegral_high_le {c : ℝ} (T : ℝ → ℝ≥0∞) (hT : Measurable T) :
    (∫⁻ z, hiW T z) ^ 2 ≤
      (ENNReal.ofReal 2 * ∫⁻ z, bw (-(2 * c)) z) * ∫⁻ z, bw (2 * (c - 1)) z * T z ^ 2 := by
  have hχ : Measurable (lowSetᶜ.indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_one.indicator measurableSet_lowSet.compl
  have hf : Measurable fun z => lowSetᶜ.indicator (1 : ℝ → ℝ≥0∞) z * invq z * bw (1 - c) z :=
    (hχ.mul measurable_invq).mul (measurable_bw _)
  have hg : Measurable fun z => bw (c - 1) z * T z := (measurable_bw _).mul hT
  have e : ∀ z, hiW T z =
      (lowSetᶜ.indicator 1 z * invq z * bw (1 - c) z) * (bw (c - 1) z * T z) := fun z => by
    have h1 : bw (1 - c) z * bw (c - 1) z = 1 := by
      rw [bw_mul, show 1 - c + (c - 1) = 0 by ring, bw_zero]
    calc hiW T z = hiW T z * (bw (1 - c) z * bw (c - 1) z) := by rw [h1, mul_one]
      _ = _ := by unfold hiW; ring
  rw [lintegral_congr e]
  refine (sq_lintegral_mul_le _ _ hf hg).trans (mul_le_mul' ?_ (le_of_eq ?_))
  · rw [← lintegral_const_mul _ (measurable_bw _)]
    refine lintegral_mono fun z => ?_
    rw [mul_pow, mul_pow, indicator_one_sq, bw_sq]
    by_cases h : z ∈ lowSet
    · have h' : z ∉ lowSetᶜ := fun hh => hh h
      simp [h']
    · have h' : z ∈ lowSetᶜ := h
      rw [Set.indicator_of_mem h', Pi.one_apply, one_mul]
      calc invq z ^ 2 * bw (2 * (1 - c)) z ≤ (ENNReal.ofReal 2 * bw (-2) z) * bw (2 * (1 - c)) z := by
            gcongr
            exact invq_sq_le_high h
        _ = ENNReal.ofReal 2 * bw (-(2 * c)) z := by
            rw [mul_assoc, bw_mul, show -2 + 2 * (1 - c) = -(2 * c) by ring]
  · exact lintegral_congr fun z => by rw [mul_pow, bw_sq]

/-- Peetre: `⟨2πx⟩^c ≤ (1+|2π(x-z)|)^c (1+|2πz|)^c`. -/
theorem bw_le_peetre {c : ℝ} (hc : 0 ≤ c) (x z : ℝ) :
    bw c x ≤ ENNReal.ofReal ((1 + |2 * Real.pi * (x - z)|) ^ c) *
      ENNReal.ofReal ((1 + |2 * Real.pi * z|) ^ c) := by
  rw [bw, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  refine Real.rpow_le_rpow (brk_pos _).le ?_ hc
  have h1 := brk_le_one_add_abs (2 * Real.pi * x)
  have h2 : |2 * Real.pi * x| ≤ |2 * Real.pi * (x - z)| + |2 * Real.pi * z| := by
    have := abs_add_le (2 * Real.pi * (x - z)) (2 * Real.pi * z)
    rwa [show 2 * Real.pi * (x - z) + 2 * Real.pi * z = 2 * Real.pi * x by ring] at this
  nlinarith [abs_nonneg (2 * Real.pi * (x - z)), abs_nonneg (2 * Real.pi * z)]

theorem P3_bound (Ψ : 𝓢(ℝ, ℂ)) {c : ℝ} (hc : 0 ≤ c) (H : ℝ → ℝ≥0∞) (x : ℝ) :
    bw c x * ∫⁻ z, ‖Ψ (x - z)‖ₑ * H z ≤
      ∫⁻ z, cutoffProfile Ψ c (x - z) * (ENNReal.ofReal ((1 + |2 * Real.pi * z|) ^ c) * H z) := by
  rw [← lintegral_const_mul' (bw c x) _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun z => ?_
  unfold cutoffProfile
  calc bw c x * (‖Ψ (x - z)‖ₑ * H z) ≤ (ENNReal.ofReal ((1 + |2 * Real.pi * (x - z)|) ^ c) *
        ENNReal.ofReal ((1 + |2 * Real.pi * z|) ^ c)) * (‖Ψ (x - z)‖ₑ * H z) :=
        enn_mul_le_right (bw_le_peetre hc x z) _
    _ = _ := by ring

/-- Oscillatory part (Young/Schur after Peetre). -/
theorem lintegral_P3_le (Ψ : 𝓢(ℝ, ℂ)) {c : ℝ} (hc : 0 ≤ c) (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ x, (bw c x * ∫⁻ z, ‖Ψ (x - z)‖ₑ * H z) ^ 2 ≤
      (∫⁻ u, cutoffProfile Ψ c u) * (∫⁻ u, cutoffProfile Ψ c u) *
        ∫⁻ z, (ENNReal.ofReal ((1 + |2 * Real.pi * z|) ^ c) * H z) ^ 2 := by
  have hφ : Measurable fun z => ENNReal.ofReal ((1 + |2 * Real.pi * z|) ^ c) * H z :=
    (ENNReal.measurable_ofReal.comp
      ((by fun_prop : Continuous fun z : ℝ => 1 + |2 * Real.pi * z|).measurable.pow_const c)).mul hH
  have h := lintegral_sq_conv_le (fun _ => 1) (cutoffProfile Ψ c) _ measurable_const
    (measurable_cutoffProfile Ψ c) hφ (∫⁻ u, cutoffProfile Ψ c u) (fun y => by
      simp only [one_pow, one_mul]
      exact le_of_eq (lintegral_sub_right_eq_self _ y))
  simp only [one_pow, one_mul] at h
  refine le_trans (lintegral_mono fun x => ?_) h
  exact pow_le_pow_left₀ bot_le (P3_bound Ψ hc H x) 2

theorem phi_sq_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (T : ℝ → ℝ≥0∞) (z : ℝ) :
    (ENNReal.ofReal ((1 + |2 * Real.pi * z|) ^ c) * hiW T z) ^ 2 ≤
      ENNReal.ofReal 8 * (bw (2 * (c - 1)) z * T z ^ 2) := by
  unfold hiW
  by_cases h : z ∈ lowSet
  · have h' : z ∉ lowSetᶜ := fun hh => hh h
    simp [h']
  · have h' : z ∈ lowSetᶜ := h
    rw [Set.indicator_of_mem h', Pi.one_apply, one_mul]
    have h1 : ENNReal.ofReal ((1 + |2 * Real.pi * z|) ^ c) ^ 2 ≤
        ENNReal.ofReal 4 * bw (2 * c) z := by
      rw [← ENNReal.ofReal_pow (by positivity), bw, ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have hb1 := one_le_brk (2 * Real.pi * z)
      have hb2 := abs_le_brk (2 * Real.pi * z)
      have hle : 1 + |2 * Real.pi * z| ≤ 2 * brk (2 * Real.pi * z) := by linarith
      calc ((1 + |2 * Real.pi * z|) ^ c) ^ 2 = (1 + |2 * Real.pi * z|) ^ (2 * c) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            congr 1
            push_cast
            ring
        _ ≤ (2 * brk (2 * Real.pi * z)) ^ (2 * c) :=
            Real.rpow_le_rpow (by positivity) hle (by linarith)
        _ =2 ^ (2 * c) * brk (2 * Real.pi * z) ^ (2 * c) :=
            Real.mul_rpow (by norm_num) (brk_pos _).le
        _ ≤ 4 * brk (2 * Real.pi * z) ^ (2 * c) := by
            gcongr
            calc (2 : ℝ) ^ (2 * c) ≤ 2 ^ (2 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 4 := by rw [Real.rpow_two]; norm_num
    have h2 := invq_sq_le_high h
    calc _ = ENNReal.ofReal ((1 + |2 * Real.pi * z|) ^ c) ^ 2 * invq z ^ 2 * T z ^ 2 := by ring
      _ ≤ (ENNReal.ofReal 4 * bw (2 * c) z) * (ENNReal.ofReal 2 * bw (-2) z) * T z ^ 2 := by
          gcongr
      _ = ENNReal.ofReal 4 * ENNReal.ofReal 2 * (bw (2 * c) z * bw (-2) z * T z ^ 2) := by ring
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by norm_num), bw_mul,
            show 2 * c + -2 = 2 * (c - 1) by ring]
          norm_num

theorem lintegral_bw_decay_le {c : ℝ} (hc1 : c ≤ 1) :
    ∫⁻ x, bw (2 * c) x * bw (-2) x ^ 2 ≤ ∫⁻ x, bw (-2) x := by
  refine lintegral_mono fun x => ?_
  rw [bw_sq, bw_mul]
  exact bw_mono (by linarith) x

/-- **Scalar fixed-cutoff Duhamel bound, Fourier side** (general measurable `T ≥ 0`). -/
theorem duhamel_kernel_aux {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1) (Ψ : 𝓢(ℝ, ℂ))
    (T : ℝ → ℝ≥0∞) (hT : Measurable T) :
    ∫⁻ x, bw (2 * c) x * (∫⁻ z, ‖duhKer Ψ x z‖ₑ * T z) ^ 2 ≤
      (4 * (ENNReal.ofReal (duhA Ψ) ^ 2 * (ENNReal.ofReal 2 *
          ENNReal.ofReal (1 + 2 * Real.pi)) * ∫⁻ x, bw (-2) x) +
        4 * (ENNReal.ofReal 2 * (∫⁻ z, bw (-(2 * c)) z) *
          (ENNReal.ofReal (decayC Ψ) ^ 2 * ∫⁻ x, bw (-2) x)) +
        4 * ((∫⁻ u, cutoffProfile Ψ c u) * (∫⁻ u, cutoffProfile Ψ c u) * ENNReal.ofReal 8)) *
        ∫⁻ z, bw (2 * (c - 1)) z * T z ^ 2 := by
  have hc0 : 0 ≤ c := by linarith
  have hH := measurable_hiW hT
  have hw1 : Measurable fun x => bw (2 * c) x * bw (-2) x ^ 2 :=
    (measurable_bw _).mul ((measurable_bw _).pow_const 2)
  have hw2 : Measurable fun x => bw (2 * c) x * ‖Ψ x‖ₑ ^ 2 :=
    (measurable_bw _).mul (Ψ.continuous.measurable.enorm.pow_const 2)
  set a : ℝ≥0∞ := ENNReal.ofReal (duhA Ψ) with ha
  set d : ℝ≥0∞ := ENNReal.ofReal (decayC Ψ) with hd
  set Il : ℝ≥0∞ := ∫⁻ z, lowSet.indicator 1 z * T z with hIl
  set Ih : ℝ≥0∞ := ∫⁻ z, hiW T z with hIh
  set N : ℝ≥0∞ := ∫⁻ z, bw (2 * (c - 1)) z * T z ^ 2 with hN
  have step1 : ∀ x, bw (2 * c) x * (∫⁻ z, ‖duhKer Ψ x z‖ₑ * T z) ^ 2 ≤
      (4 * (a ^ 2 * Il ^ 2) * (bw (2 * c) x * bw (-2) x ^ 2) +
        4 * Ih ^ 2 * (bw (2 * c) x * ‖Ψ x‖ₑ ^ 2)) +
      4 * (bw c x * ∫⁻ z, ‖Ψ (x - z)‖ₑ * hiW T z) ^ 2 := fun x => by
    calc bw (2 * c) x * (∫⁻ z, ‖duhKer Ψ x z‖ₑ * T z) ^ 2
        ≤ bw (2 * c) x * (a * bw (-2) x * Il + ‖Ψ x‖ₑ * Ih +
            ∫⁻ z, ‖Ψ (x - z)‖ₑ * hiW T z) ^ 2 := by
          gcongr
          exact lintegral_duhKer_le Ψ T hT x
      _ ≤ bw (2 * c) x * (4 * ((a * bw (-2) x * Il) ^ 2 + (‖Ψ x‖ₑ * Ih) ^ 2 +
            (∫⁻ z, ‖Ψ (x - z)‖ₑ * hiW T z) ^ 2)) := by
          gcongr
          exact add3_sq_le _ _ _
      _ = _ := by rw [mul_pow (bw c x), bw_sq c x]; ring
  have hIlb : Il ^ 2 ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (1 + 2 * Real.pi) * N) :=
    sq_lintegral_low_le hc.le hc1 T hT
  have hIhb : Ih ^ 2 ≤ (ENNReal.ofReal 2 * ∫⁻ z, bw (-(2 * c)) z) * N :=
    sq_lintegral_high_le T hT
  have hW1 := lintegral_bw_decay_le hc1
  have hW2 : ∫⁻ x, bw (2 * c) x * ‖Ψ x‖ₑ ^ 2 ≤ d ^ 2 * ∫⁻ x, bw (-2) x := by
    calc ∫⁻ x, bw (2 * c) x * ‖Ψ x‖ₑ ^ 2 ≤ ∫⁻ x, d ^ 2 * (bw (2 * c) x * bw (-2) x ^ 2) :=
          lintegral_mono fun x => by
            calc bw (2 * c) x * ‖Ψ x‖ₑ ^ 2 ≤ bw (2 * c) x * (d * bw (-2) x) ^ 2 := by
                  gcongr
                  exact enorm_le_decayC Ψ x
              _ = _ := by ring
      _ = d ^ 2 * ∫⁻ x, bw (2 * c) x * bw (-2) x ^ 2 := lintegral_const_mul _ hw1
      _ ≤ d ^ 2 * ∫⁻ x, bw (-2) x := enn_mul_le_left hW1 _
  have hP3 : ∫⁻ x, (bw c x * ∫⁻ z, ‖Ψ (x - z)‖ₑ * hiW T z) ^ 2 ≤
      (∫⁻ u, cutoffProfile Ψ c u) * (∫⁻ u, cutoffProfile Ψ c u) * (ENNReal.ofReal 8 * N) := by
    refine (lintegral_P3_le Ψ hc0 _ hH).trans (enn_mul_le_left ?_ _)
    have hm : Measurable fun z => bw (2 * (c - 1)) z * T z ^ 2 := (measurable_bw _).mul (hT.pow_const 2)
    rw [hN, ← lintegral_const_mul _ hm]
    exact lintegral_mono fun z => phi_sq_le hc0 hc1 T z
  calc ∫⁻ x, bw (2 * c) x * (∫⁻ z, ‖duhKer Ψ x z‖ₑ * T z) ^ 2
      ≤ ∫⁻ x, (4 * (a ^ 2 * Il ^ 2) * (bw (2 * c) x * bw (-2) x ^ 2) +
          4 * Ih ^ 2 * (bw (2 * c) x * ‖Ψ x‖ₑ ^ 2)) +
        4 * (bw c x * ∫⁻ z, ‖Ψ (x - z)‖ₑ * hiW T z) ^ 2 := lintegral_mono step1
    _ = (4 * (a ^ 2 * Il ^ 2) * (∫⁻ x, bw (2 * c) x * bw (-2) x ^ 2) +
          4 * Ih ^ 2 * (∫⁻ x, bw (2 * c) x * ‖Ψ x‖ₑ ^ 2)) +
        4 * ∫⁻ x, (bw c x * ∫⁻ z, ‖Ψ (x - z)‖ₑ * hiW T z) ^ 2 := by
        have hm1 : Measurable fun x => 4 * (a ^ 2 * Il ^ 2) * (bw (2 * c) x * bw (-2) x ^ 2) +
            4 * Ih ^ 2 * (bw (2 * c) x * ‖Ψ x‖ₑ ^ 2) := (hw1.const_mul _).add (hw2.const_mul _)
        have hm2 : Measurable fun x => 4 * (a ^ 2 * Il ^ 2) * (bw (2 * c) x * bw (-2) x ^ 2) :=
          hw1.const_mul _
        rw [lintegral_add_left hm1, lintegral_add_left hm2, lintegral_const_mul _ hw1,
          lintegral_const_mul _ hw2, lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ (4 * (a ^ 2 * (ENNReal.ofReal 2 * (ENNReal.ofReal (1 + 2 * Real.pi) * N))) *
            (∫⁻ x, bw (-2) x) +
          4 * ((ENNReal.ofReal 2 * ∫⁻ z, bw (-(2 * c)) z) * N) * (d ^ 2 * ∫⁻ x, bw (-2) x)) +
        4 * ((∫⁻ u, cutoffProfile Ψ c u) * (∫⁻ u, cutoffProfile Ψ c u) *
          (ENNReal.ofReal 8 * N)) :=
        add_le_add (add_le_add (mul_le_mul' (enn_mul_le_left (enn_mul_le_left hIlb _) _) hW1)
          (mul_le_mul' (enn_mul_le_left hIhb _) hW2)) (enn_mul_le_left hP3 _)
    _ = _ := by ring

/-- **Scalar fixed-cutoff Duhamel bound, Fourier side** (`1/2 < c ≤ 1`, any Schwartz `Ψ`). -/
theorem duhamel_kernel_bound {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1) (Ψ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ θ : ℝ → ℂ, Measurable θ →
      ∫⁻ x, bw (2 * c) x * (∫⁻ z, ‖duhKer Ψ x z‖ₑ * ‖θ z‖ₑ) ^ 2 ≤
        C * ∫⁻ z, bw (2 * (c - 1)) z * ‖θ z‖ₑ ^ 2 := by
  refine ⟨_, ?_, fun θ hθ => duhamel_kernel_aux hc hc1 Ψ (fun z => ‖θ z‖ₑ) hθ.enorm⟩
  have hE := (lintegral_bw_lt_top (by norm_num : (1 : ℝ) < 2)).ne
  have hE' := (lintegral_bw_lt_top (by linarith : (1 : ℝ) < 2 * c)).ne
  have hR := (lintegral_cutoffProfile_lt_top Ψ hc1).ne
  have h4 : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨?_, ?_⟩, ?_⟩
  · exact ENNReal.mul_ne_top h4 (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) hE)
  · exact ENNReal.mul_ne_top h4 (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE')
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hE))
  · exact ENNReal.mul_ne_top h4 (ENNReal.mul_ne_top (ENNReal.mul_ne_top hR hR)
      ENNReal.ofReal_ne_top)

end LiebLiniger.FixedPeriod.ALLS.PdeB
