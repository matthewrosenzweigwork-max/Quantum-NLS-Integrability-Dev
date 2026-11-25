import NlsGge.Hierarchy.ALMonodromyAlgebra38
import NlsGge.Hierarchy.ALFloquetMonotone38
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Exponential

/-! Batch 38, exterior branch of the AL Floquet multiplier (paper/v2.tex D-section, `D:eq:pAL`).
In `ζ = 1/z` on the unit ball: `t(ζ) = ζ^L tr M(1/ζ)` is an even polynomial, `D = t² - 4ζ^{2L}`
is nonvanishing, `s = √D` holomorphic, and `g = (t+s)/2` satisfies `ζ^{-L} g = w₊` with
`‖w₊‖ > 1`. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open scoped Matrix
open Filter Topology Metric Set

/-! ### Generic lemmas -/

theorem exists_eigen38 (M : Matrix (Fin 2) (Fin 2) ℂ) (hdet : M.det = 1) (w : ℂ)
    (hw : w ^ 2 - M.trace * w + 1 = 0) : ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.mulVec v = w • v := by
  have h0 : (M - w • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
    rw [Matrix.det_fin_two] at hdet ⊢
    rw [Matrix.trace_fin_two] at hw
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
      ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true, smul_eq_mul, mul_one,
      mul_zero, one_ne_zero, sub_zero]
    linear_combination hdet + hw
  obtain ⟨v, hv, h⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at h
  simpa [Matrix.smul_mulVec] using h

theorem isPreconnected_punctured_ball38 : IsPreconnected (ball (0 : ℂ) 1 \ {0}) := by
  have h : ball (0 : ℂ) 1 \ {0} = Complex.exp '' {z : ℂ | z.re < 0} := by
    ext ζ
    constructor
    · rintro ⟨hb, h0⟩
      have h0' : ζ ≠ 0 := h0
      have hn : ‖ζ‖ < 1 := by simpa using hb
      refine ⟨Complex.log ζ, ?_, Complex.exp_log h0'⟩
      show (Complex.log ζ).re < 0
      rw [Complex.log_re]
      exact Real.log_neg (norm_pos_iff.mpr h0') hn
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, Complex.exp_ne_zero z⟩
      rw [mem_ball_zero_iff, Complex.norm_exp]
      have := Real.exp_lt_exp.2 hz
      simpa using this
  rw [h]
  exact (convex_halfSpace_re_lt (0 : ℝ)).isPreconnected.image _
    Complex.continuous_exp.continuousOn

/-- Holomorphic square root on the unit ball of a nonvanishing entire function. -/
theorem exists_sqrt_ball38 (D : ℂ → ℂ) (hD : Differentiable ℂ D)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, D z ≠ 0) (c : ℂ) (hc : c ^ 2 = D 0) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (ball (0 : ℂ) 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, s z ^ 2 = D z) ∧ s 0 = c := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h] at hc; exact hne 0 (mem_ball_self one_pos) (by rw [← hc]; ring)
  have hf : DifferentiableOn ℂ (fun z => deriv D z / D z) (ball (0 : ℂ) 1) := by
    intro z hz
    exact ((((hD.analyticAt z).deriv).differentiableAt).div (hD z) (hne z hz)).differentiableWithinAt
  obtain ⟨h, h0, hh⟩ := hf.isExactOn_ball.with_val_at 0 (2 * Complex.log c)
  have hB : ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt h (deriv D z / D z) z := hh
  have hG : ∀ z ∈ ball (0 : ℂ) 1,
      HasDerivAt (fun z => D z * Complex.exp (-h z)) 0 z := by
    intro z hz
    have h1 := (hD z).hasDerivAt
    have h2 := ((hB z hz).neg).cexp
    have h3 := h1.mul h2
    convert h3 using 1
    field_simp [hne z hz]
    ring
  have hconst : ∀ z ∈ ball (0 : ℂ) 1, D z * Complex.exp (-h z) = 1 := by
    intro z hz
    have := isOpen_ball.is_const_of_deriv_eq_zero (𝕜 := ℂ) (f := fun z => D z * Complex.exp (-h z))
      (convex_ball (0 : ℂ) 1).isPreconnected
      (fun y hy => (hG y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hG y hy).deriv) hz (mem_ball_self one_pos)
    rw [this, h0]
    have : Complex.exp (-(2 * Complex.log c)) = (c ^ 2)⁻¹ := by
      rw [Complex.exp_neg, show 2 * Complex.log c = Complex.log c + Complex.log c by ring,
        Complex.exp_add, Complex.exp_log hc0]; ring_nf
    rw [this, ← hc]
    exact mul_inv_cancel₀ (pow_ne_zero 2 hc0)
  refine ⟨fun z => Complex.exp (h z / 2), ?_, ?_, ?_⟩
  · intro z hz
    have : DifferentiableOn ℂ (fun z => Complex.exp (h z / 2)) (ball (0 : ℂ) 1) := fun y hy =>
      (((hB y hy).differentiableAt.div_const 2).cexp).differentiableWithinAt
    exact this.analyticOnNhd isOpen_ball z hz
  · intro z hz
    rw [← Complex.exp_nat_mul]
    have e : D z = Complex.exp (h z) := by
      have := hconst z hz
      have hx : Complex.exp (-h z) * Complex.exp (h z) = 1 := by
        rw [← Complex.exp_add]; simp
      calc D z = D z * (Complex.exp (-h z) * Complex.exp (h z)) := by rw [hx, mul_one]
        _ = (D z * Complex.exp (-h z)) * Complex.exp (h z) := by ring
        _ = _ := by rw [this, one_mul]
    rw [e]; congr 1; push_cast; ring
  · simp only [h0]
    rw [show 2 * Complex.log c / 2 = Complex.log c by ring, Complex.exp_log hc0]

/-! ### Definitions -/

open Classical in
/-- Laurent coefficients of the trace (chosen). -/
def alExtCoeff38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) : ℕ → ℂ :=
  if h : IsALField38 α then Classical.choose (alMonodromy38_trace_laurent h) else fun _ => 0

/-- `t(ζ) = Σ_k c_k ζ^{2k}`, i.e. `ζ^L tr M(1/ζ)`. -/
def alExtT38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (ζ : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (L + 1), alExtCoeff38 α k * ζ ^ (2 * k)

/-- `D(ζ) = t(ζ)² - 4 ζ^{2L}`. -/
def alExtD38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (ζ : ℂ) : ℂ :=
  alExtT38 α ζ ^ 2 - 4 * ζ ^ (2 * L)

theorem alExtCoeff38_spec {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    (∀ z : ℂ, z ≠ 0 → Matrix.trace (alMonodromy38 α z) =
        ∑ k ∈ Finset.range (L + 1), alExtCoeff38 α k * z ^ ((L : ℤ) - 2 * k)) ∧
      alExtCoeff38 α 0 = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) := by
  unfold alExtCoeff38
  rw [dif_pos hα]
  exact Classical.choose_spec (alMonodromy38_trace_laurent hα)

theorem alExtT38_differentiable {L : ℕ} [NeZero L] (α : ZMod L → ℂ) :
    Differentiable ℂ (alExtT38 α) := by
  unfold alExtT38
  fun_prop

theorem alExtD38_differentiable {L : ℕ} [NeZero L] (α : ZMod L → ℂ) :
    Differentiable ℂ (alExtD38 α) := by
  unfold alExtD38
  have := alExtT38_differentiable α
  fun_prop

theorem alExtT38_zero {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alExtT38 α 0 = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) := by
  unfold alExtT38
  rw [Finset.sum_eq_single 0]
  · simp [(alExtCoeff38_spec hα).2]
  · intro k _ hk
    simp [zero_pow (show 2 * k ≠ 0 by omega)]
  · intro h; simp at h

theorem alExtT38_neg {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (ζ : ℂ) :
    alExtT38 α (-ζ) = alExtT38 α ζ := by
  unfold alExtT38
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_mul, neg_sq, ← pow_mul]

theorem alExtT38_eq {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ≠ 0) : alExtT38 α ζ = ζ ^ L * Matrix.trace (alMonodromy38 α ζ⁻¹) := by
  rw [(alExtCoeff38_spec hα).1 ζ⁻¹ (inv_ne_zero hζ), Finset.mul_sum]
  unfold alExtT38
  refine Finset.sum_congr rfl fun k _ => ?_
  have : ζ ^ (L : ℤ) * (ζ⁻¹) ^ ((L : ℤ) - 2 * k) = ζ ^ (2 * k) := by
    rw [inv_zpow', ← zpow_add₀ hζ]
    have : (L : ℤ) + -((L : ℤ) - 2 * k) = ((2 * k : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_natCast]
  rw [← this, zpow_natCast]; ring

theorem alExtD38_zero {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alExtD38 α 0 = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) ^ 2 := by
  unfold alExtD38
  rw [alExtT38_zero hα, zero_pow (show 2 * L ≠ 0 from by have := NeZero.ne L; omega)]
  ring

theorem alExtD38_ne_zero {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) : alExtD38 α ζ ≠ 0 := by
  by_cases h0 : ζ = 0
  · subst h0
    rw [alExtD38_zero hα]
    exact pow_ne_zero 2 (by exact_mod_cast (Real.exp_pos _).ne')
  · intro hD
    have hn : ‖ζ‖ < 1 := by simpa using hζ
    have hz1 : 1 < ‖ζ⁻¹‖ := by rw [norm_inv]; exact one_lt_inv₀ (norm_pos_iff.mpr h0) |>.2 hn
    set M := alMonodromy38 α ζ⁻¹ with hM
    have hzL : ζ ^ L ≠ 0 := pow_ne_zero _ h0
    have htr : M.trace ^ 2 = 4 := by
      unfold alExtD38 at hD
      rw [alExtT38_eq hα h0] at hD
      have : (ζ ^ L) ^ 2 * (M.trace ^ 2 - 4) = 0 := by
        linear_combination hD
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (pow_eq_zero_iff (two_ne_zero) |>.1 h) hzL
      · linear_combination h
    have hdet := det_alMonodromy38 hα (inv_ne_zero h0)
    obtain ⟨v, hv, hMv⟩ := exists_eigen38 M hdet (M.trace / 2) (by linear_combination (-1/4 : ℂ) * htr)
    have hw1 : ‖M.trace / 2‖ = 1 := by
      have : (M.trace / 2) ^ 2 = 1 := by linear_combination (1/4 : ℂ) * htr
      have h2 : ‖M.trace / 2‖ ^ 2 = 1 := by rw [← norm_pow, this, norm_one]
      nlinarith [norm_nonneg (M.trace / 2)]
    exact no_unimodular_multiplier38 α hα ζ⁻¹ hz1 _ v hv hMv hw1

theorem exists_alExtS38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (ball (0 : ℂ) 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, s z ^ 2 = alExtD38 α z) ∧
      s 0 = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) :=
  exists_sqrt_ball38 _ (alExtD38_differentiable α) (fun _ hz => alExtD38_ne_zero hα hz) _
    (alExtD38_zero hα).symm

open Classical in
/-- Holomorphic square root of `D`. -/
def alExtS38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) : ℂ → ℂ :=
  if h : IsALField38 α then Classical.choose (exists_alExtS38 h) else fun _ => 0

theorem alExtS38_spec {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    AnalyticOnNhd ℂ (alExtS38 α) (ball (0 : ℂ) 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, alExtS38 α z ^ 2 = alExtD38 α z) ∧
      alExtS38 α 0 = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) := by
  unfold alExtS38
  rw [dif_pos hα]
  exact Classical.choose_spec (exists_alExtS38 hα)

/-- The exterior branch `g = (t + s)/2` in `ζ = 1/z`. -/
def alExteriorG38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (ζ : ℂ) : ℂ :=
  (alExtT38 α ζ + alExtS38 α ζ) / 2

/-! ### Properties -/

theorem alExteriorG38_analytic {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    AnalyticOnNhd ℂ (alExteriorG38 α) (ball (0 : ℂ) 1) := by
  intro z hz
  have ht : AnalyticAt ℂ (alExtT38 α) z := (alExtT38_differentiable α).analyticAt z
  exact (ht.add ((alExtS38_spec hα).1 z hz)).div_const

theorem alExteriorG38_zero {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alExteriorG38 α 0 = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) := by
  unfold alExteriorG38
  rw [alExtT38_zero hα, (alExtS38_spec hα).2.2]; ring

theorem alExteriorG38_sq {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) :
    alExteriorG38 α ζ ^ 2 - alExtT38 α ζ * alExteriorG38 α ζ + ζ ^ (2 * L) = 0 := by
  have hs := (alExtS38_spec hα).2.1 ζ hζ
  unfold alExteriorG38; unfold alExtD38 at hs
  linear_combination (1 / 4 : ℂ) * hs

theorem alExteriorG38_ne_zero {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) : alExteriorG38 α ζ ≠ 0 := by
  by_cases h0 : ζ = 0
  · subst h0
    rw [alExteriorG38_zero hα]
    exact_mod_cast (Real.exp_pos _).ne'
  · intro h
    have := alExteriorG38_sq hα hζ
    rw [h] at this
    simp at this
    exact h0 this.1

theorem alExtS38_neg {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) : alExtS38 α (-ζ) = alExtS38 α ζ := by
  obtain ⟨hs, hsq, hs0⟩ := alExtS38_spec hα
  have hneg : ∀ z ∈ ball (0 : ℂ) 1, -z ∈ ball (0 : ℂ) 1 := by
    intro z hz; simpa using hz
  have hDneg : ∀ z, alExtD38 α (-z) = alExtD38 α z := by
    intro z; unfold alExtD38
    rw [alExtT38_neg, pow_mul, neg_sq, ← pow_mul]
  have hanalyt : AnalyticOnNhd ℂ (fun z => alExtS38 α (-z)) (ball (0 : ℂ) 1) := by
    intro z hz
    exact (hs (-z) (hneg z hz)).comp (analyticAt_id.neg)
  have hu : AnalyticOnNhd ℂ (fun z => alExtS38 α (-z) - alExtS38 α z) (ball (0 : ℂ) 1) :=
    hanalyt.sub hs
  have hv : AnalyticOnNhd ℂ (fun z => alExtS38 α (-z) + alExtS38 α z) (ball (0 : ℂ) 1) :=
    hanalyt.add hs
  have hprod : ∀ z ∈ ball (0 : ℂ) 1,
      (alExtS38 α (-z) - alExtS38 α z) * (alExtS38 α (-z) + alExtS38 α z) = 0 := by
    intro z hz
    have h1 := hsq (-z) (hneg z hz)
    have h2 := hsq z hz
    rw [hDneg] at h1
    linear_combination h1 - h2
  have h00 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hs0ne : alExtS38 α 0 ≠ 0 := by
    rw [hs0]; exact_mod_cast (Real.exp_pos _).ne'
  by_cases hfr : ∃ᶠ z in 𝓝[≠] (0 : ℂ), alExtS38 α (-z) - alExtS38 α z = 0
  · have := hu.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_ball (0 : ℂ) 1).isPreconnected h00 hfr hζ
    simpa [sub_eq_zero] using this
  · exfalso
    have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), alExtS38 α (-z) - alExtS38 α z ≠ 0 := by
      simpa [Filter.not_frequently] using hfr
    have hin : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball (0 : ℂ) 1 :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds h00)
    have hvz : ∃ᶠ z in 𝓝[≠] (0 : ℂ), alExtS38 α (-z) + alExtS38 α z = 0 := by
      refine (hev.and hin).frequently.mono ?_
      rintro z ⟨h1, h2⟩
      exact (mul_eq_zero.mp (hprod z h2)).resolve_left h1
    have := hv.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_ball (0 : ℂ) 1).isPreconnected h00 hvz h00
    simp at this
    exact hs0ne this

theorem alExteriorG38_neg {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) : alExteriorG38 α (-ζ) = alExteriorG38 α ζ := by
  unfold alExteriorG38
  rw [alExtT38_neg, alExtS38_neg hα hζ]

/-- The exterior multiplier `w₊ = ζ^{-L} g(ζ)`. -/
def alExtW38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (ζ : ℂ) : ℂ :=
  (ζ ^ L)⁻¹ * alExteriorG38 α ζ

theorem alExtW38_root {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) (h0 : ζ ≠ 0) :
    alExtW38 α ζ ^ 2 - Matrix.trace (alMonodromy38 α ζ⁻¹) * alExtW38 α ζ + 1 = 0 := by
  have hzL : ζ ^ L ≠ 0 := pow_ne_zero _ h0
  have key := alExteriorG38_sq hα hζ
  rw [alExtT38_eq hα h0] at key
  unfold alExtW38
  have e : ζ ^ (2 * L) = (ζ ^ L) ^ 2 := by ring
  rw [e] at key
  set g := alExteriorG38 α ζ
  set tr := Matrix.trace (alMonodromy38 α ζ⁻¹)
  have : ((ζ ^ L)⁻¹ * g) ^ 2 - tr * ((ζ ^ L)⁻¹ * g) + 1 =
      ((ζ ^ L)⁻¹) ^ 2 * (g ^ 2 - ζ ^ L * tr * g + (ζ ^ L) ^ 2) := by
    field_simp
  rw [this, key, mul_zero]

theorem alExtW38_eigen {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) (h0 : ζ ≠ 0) :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ (alMonodromy38 α ζ⁻¹).mulVec v = alExtW38 α ζ • v :=
  exists_eigen38 _ (det_alMonodromy38 hα (inv_ne_zero h0)) _ (alExtW38_root hα hζ h0)

theorem alExtW38_norm_ne_one {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) (h0 : ζ ≠ 0) : ‖alExtW38 α ζ‖ ≠ 1 := by
  have hn : ‖ζ‖ < 1 := by simpa using hζ
  have hz1 : 1 < ‖ζ⁻¹‖ := by rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.mpr h0)).2 hn
  obtain ⟨v, hv, h⟩ := alExtW38_eigen hα hζ h0
  exact no_unimodular_multiplier38 α hα ζ⁻¹ hz1 _ v hv h

/-- Main statement: on `0 < ‖ζ‖ < 1`, `w₊ = ζ^{-L} g(ζ)` is an eigenvalue of `M(1/ζ)`, a root of
`w² - tr·w + 1`, and has modulus `> 1`. -/
theorem alExteriorG38_multiplier {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α)
    {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) (h0 : ζ ≠ 0) :
    (∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      (alMonodromy38 α ζ⁻¹).mulVec v = ((ζ ^ L)⁻¹ * alExteriorG38 α ζ) • v) ∧
    ((ζ ^ L)⁻¹ * alExteriorG38 α ζ) ^ 2 -
      Matrix.trace (alMonodromy38 α ζ⁻¹) * ((ζ ^ L)⁻¹ * alExteriorG38 α ζ) + 1 = 0 ∧
    1 < ‖(ζ ^ L)⁻¹ * alExteriorG38 α ζ‖ := by
  refine ⟨alExtW38_eigen hα hζ h0, alExtW38_root hα hζ h0, ?_⟩
  have hL : L ≠ 0 := NeZero.ne L
  set P : Set ℂ := ball (0 : ℂ) 1 \ {0} with hP
  have hPc : IsPreconnected P := isPreconnected_punctured_ball38
  have hgc : ContinuousOn (alExteriorG38 α) (ball (0 : ℂ) 1) :=
    (alExteriorG38_analytic hα).continuousOn
  have hfc : ContinuousOn (fun ζ => ‖alExtW38 α ζ‖ - 1) P := by
    have h1 : ContinuousOn (fun ζ : ℂ => (ζ ^ L)⁻¹) P :=
      (continuousOn_pow L).inv₀ (fun x hx => pow_ne_zero _ hx.2)
    exact ((h1.mul (hgc.mono sdiff_subset)).norm).sub continuousOn_const
  have hne : ∀ x ∈ P, ‖alExtW38 α x‖ - 1 ≠ 0 := fun x hx =>
    sub_ne_zero.mpr (alExtW38_norm_ne_one hα hx.1 hx.2)
  -- a point of P where it is large
  have hg0 : alExteriorG38 α 0 ≠ 0 := alExteriorG38_ne_zero hα (mem_ball_self one_pos)
  set m : ℝ := ‖alExteriorG38 α 0‖ / 2 with hm
  have hmpos : 0 < m := by have := norm_pos_iff.mpr hg0; rw [hm]; linarith
  have e1 : ∀ᶠ x in 𝓝 (0 : ℂ), m < ‖alExteriorG38 α x‖ := by
    have hc : ContinuousAt (alExteriorG38 α) 0 :=
      hgc.continuousAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
    exact hc.norm.eventually (lt_mem_nhds (by rw [hm]; have := norm_pos_iff.mpr hg0; linarith))
  have e2 : ∀ᶠ x in 𝓝 (0 : ℂ), ‖x‖ ^ L < m := by
    have hc : ContinuousAt (fun x : ℂ => ‖x‖ ^ L) 0 := (continuous_norm.pow L).continuousAt
    exact hc.eventually (gt_mem_nhds (by simpa [zero_pow hL] using hmpos))
  have e3 : ∀ᶠ x in 𝓝 (0 : ℂ), x ∈ ball (0 : ℂ) 1 := isOpen_ball.mem_nhds (mem_ball_self one_pos)
  obtain ⟨a, ⟨⟨ha1, ha2⟩, ha3⟩, ha4⟩ :=
    (((e1.and e2).and e3).filter_mono (nhdsWithin_le_nhds (s := ({0} : Set ℂ)ᶜ))
      |>.and self_mem_nhdsWithin).exists
  have haP : a ∈ P := ⟨ha3, ha4⟩
  have hpos : 0 < ‖alExtW38 α a‖ - 1 := by
    have hapos : 0 < ‖a‖ ^ L := pow_pos (norm_pos_iff.mpr ha4) L
    have : 1 < ‖alExtW38 α a‖ := by
      unfold alExtW38
      rw [norm_mul, norm_inv, norm_pow, ← div_eq_inv_mul, lt_div_iff₀ hapos]
      linarith
    linarith
  by_contra hcon
  push Not at hcon
  have hlt : ‖alExtW38 α ζ‖ - 1 < 0 := by
    have := hne ζ ⟨hζ, h0⟩
    have h' : ‖alExtW38 α ζ‖ ≤ 1 := hcon
    show ‖alExtW38 α ζ‖ - 1 < 0
    exact lt_of_le_of_ne (by linarith) (by intro h; apply this; exact h)
  have hζP : ζ ∈ P := ⟨hζ, h0⟩
  obtain ⟨c, hcP, hc0⟩ := hPc.intermediate_value hζP haP hfc
    (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨hlt.le, hpos.le⟩)
  exact hne c hcP hc0

end NlsGge.AblowitzLadik

end
