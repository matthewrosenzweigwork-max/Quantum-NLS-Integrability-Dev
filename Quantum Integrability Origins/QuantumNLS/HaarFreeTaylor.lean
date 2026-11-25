import QuantumNLS.OffgridBessel

/-!
# R-9C3CC17D `QG:lem:haar-nonlinear-tail`, part 1: the free Taylor expansion `QG:eq:haar-free-taylor`

Source: `source-text/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:699-731` (statement) and `:732-744` (first
paragraph of the proof).

For `w ∈ Γ_0` (`OffgridBessel.Gamma0 L`, the square `max(|Re w|,|Im w|) = ω/4`, `ω = 2π/L`) and `e = e^{iwL}`:
* `aF L w X = ½(1 + e + X + (1 − e)√(1 + (2(1+e)X + X²)/(1 − e)²))` (principal square root, which is the
  Taylor square root near `1` on the radius used), the printed formula for the quadratic root near `1`;
  `aF_quad`: `aF² − (1 + e + X) aF + e = 0`;
* `FW L w X = log (aF L w X)` (principal logarithm, the Taylor logarithm near `1` on the radius used);
* **`free_taylor`**: with the explicit radius `σ = η²/(8M₁²)` (`η = 1 − e^{-π/2}`, `M₁ = 1 + e^{π/2}`) and `M = 1`,
  for every `w ∈ Γ_0` the function `X ↦ F_w(X)` is holomorphic on the closed disc `|X| ≤ σ`, takes values within
  `1/4` of `1` for `aF` (so the principal branches are the Taylor branches near `1`), and has the expansion
  `F_w(X) = Σ_d f_d(w) X^d` for `|X| < σ` with `f_0 = 0`, `f_1 = (1 − e^{iwL})^{-1}`, `|f_d(w)| ≤ M σ^{-d}`.
  The constants depend only on `L` (the fixed contour).

Route (the source's): the free discriminant `1 − e^{iwL}` is bounded below on `Γ_0` (`one_sub_ew_lower`), which
gives a common radius; the Cauchy estimate (`norm_cauchyPowerSeries_le`) on the circle `|X| = σ` gives the
coefficient bounds; `F_w'(0) = (1 − e^{iwL})^{-1}` by differentiating the explicit formula at `X = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open Complex Metric Filter Topology

namespace QuantumNLS.HaarFreeTaylor

open QuantumNLS.OffgridBessel QuantumNLS.HaarKernelFactorizationSym

/-! ## 1. Definitions -/

/-- `e^{iwL}`. -/
def ew (L : ℝ) (w : ℂ) : ℂ := exp (I * L * w)

/-- The discriminant argument `u = (2(1+e)X + X²)/(1 − e)²`. -/
def uF (L : ℝ) (w X : ℂ) : ℂ := (2 * (1 + ew L w) * X + X ^ 2) / (1 - ew L w) ^ 2

/-- The quadratic root near `1`: `½(1 + e + X + (1 − e)√(1 + u))`. -/
def aF (L : ℝ) (w X : ℂ) : ℂ :=
  (1 + ew L w + X + (1 - ew L w) * (1 + uF L w X) ^ ((2 : ℂ)⁻¹)) / 2

/-- `F_w(X) = log a(X)`. -/
def FW (L : ℝ) (w X : ℂ) : ℂ := log (aF L w X)

/-- `η = 1 − e^{-π/2}`, the lower bound of `|1 − e^{iwL}|` on `Γ_0`. -/
def etaL : ℝ := 1 - Real.exp (-(Real.pi / 2))

/-- `M₁ = 1 + e^{π/2}`. -/
def M1 : ℝ := 1 + Real.exp (Real.pi / 2)

/-- The common radius `σ = η²/(8 M₁²)`. -/
def sig : ℝ := etaL ^ 2 / (8 * M1 ^ 2)

lemma etaL_pos : 0 < etaL := by
  have := Real.exp_lt_exp.2 (show -(Real.pi / 2) < 0 by linarith [Real.pi_pos])
  rw [Real.exp_zero] at this
  unfold etaL; linarith

lemma etaL_lt_one : etaL < 1 := by
  have := Real.exp_pos (-(Real.pi / 2)); unfold etaL; linarith

lemma M1_ge : 2 ≤ M1 := by
  have := Real.one_le_exp (show 0 ≤ Real.pi / 2 by linarith [Real.pi_pos]); unfold M1; linarith

lemma sig_pos : 0 < sig := by
  have := etaL_pos; have := M1_ge; unfold sig; positivity

lemma sig_le : sig ≤ 1 / 32 := by
  have h1 := etaL_pos; have h2 := etaL_lt_one; have h3 := M1_ge
  unfold sig
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma sig_mul : sig * (8 * M1 ^ 2) = etaL ^ 2 := by
  have := M1_ge; unfold sig; field_simp

/-! ## 2. The free background on `Γ_0` -/

section Contour

variable {L : ℝ}

lemma mem_Gamma0 [Fact (0 < L)] {w : ℂ} (hw : w ∈ Gamma0 L) :
    |w.re| ≤ omegaL L / 4 ∧ |w.im| ≤ omegaL L / 4 ∧
      (|w.re| = omegaL L / 4 ∨ |w.im| = omegaL L / 4) := by
  have h : max |w.re| |w.im| = omegaL L / 4 := hw
  refine ⟨h ▸ le_max_left _ _, h ▸ le_max_right _ _, ?_⟩
  rcases le_total |w.re| |w.im| with h1 | h1
  · right; rw [max_eq_right h1] at h; exact h
  · left; rw [max_eq_left h1] at h; exact h

lemma L_omegaL (hL : 0 < L) : L * omegaL L = 2 * Real.pi := by
  unfold omegaL; field_simp

lemma norm_ew (L : ℝ) (w : ℂ) : ‖ew L w‖ = Real.exp (-(L * w.im)) := by
  rw [ew, Complex.norm_exp]; congr 1; simp

lemma norm_ew_le [Fact (0 < L)] {w : ℂ} (hw : w ∈ Gamma0 L) : ‖ew L w‖ ≤ Real.exp (Real.pi / 2) := by
  have hL : 0 < L := Fact.out
  obtain ⟨-, h2, -⟩ := mem_Gamma0 hw
  rw [norm_ew]
  refine Real.exp_le_exp.2 ?_
  have h3 : L * (omegaL L / 4) = Real.pi / 2 := by linear_combination L_omegaL hL / 4
  have h4 : -(L * w.im) ≤ L * |w.im| := by
    have := neg_abs_le w.im
    nlinarith
  have h5 : L * |w.im| ≤ L * (omegaL L / 4) := mul_le_mul_of_nonneg_left h2 hL.le
  linarith

/-- The free discriminant is bounded below on `Γ_0`: `|1 − e^{iwL}| ≥ 1 − e^{-π/2}`. -/
lemma one_sub_ew_lower [Fact (0 < L)] {w : ℂ} (hw : w ∈ Gamma0 L) : etaL ≤ ‖1 - ew L w‖ := by
  have hL : 0 < L := Fact.out
  obtain ⟨-, -, h3⟩ := mem_Gamma0 hw
  have hLω := L_omegaL hL
  have hLh : L * (omegaL L / 4) = Real.pi / 2 := by linear_combination hLω / 4
  have hpos := Real.exp_pos (-(Real.pi / 2))
  unfold etaL
  rcases h3 with h3 | h3
  · have hre : (1 - ew L w).re = 1 := by
      rw [sub_re, one_re, ew, Complex.exp_re]
      have e1 : (I * L * w).im = L * w.re := by simp
      rw [e1]
      have hc : Real.cos (L * w.re) = 0 := by
        have hω0 : (0 : ℝ) ≤ omegaL L / 4 := by
          have : 0 < omegaL L := by unfold omegaL; have := Real.pi_pos; positivity
          linarith
        rcases (abs_eq hω0).1 h3 with h | h <;> rw [h]
        · rw [hLh, Real.cos_pi_div_two]
        · rw [show L * -(omegaL L / 4) = -(Real.pi / 2) by linarith, Real.cos_neg, Real.cos_pi_div_two]
      rw [hc, mul_zero, sub_zero]
    have := Complex.abs_re_le_norm (1 - ew L w)
    rw [hre, abs_one] at this
    linarith
  · have hω : 0 ≤ omegaL L / 4 := by
      have : 0 < omegaL L := by unfold omegaL; have := Real.pi_pos; positivity
      linarith
    rcases (abs_eq hω).1 h3 with h | h
    · have hn := norm_sub_norm_le (1 : ℂ) (ew L w)
      rw [norm_one, norm_ew, h, hLh] at hn
      linarith
    · have hn := norm_sub_norm_le (ew L w) 1
      rw [norm_sub_rev, norm_one, norm_ew, h, mul_neg, neg_neg, hLh] at hn
      have := Real.add_one_le_exp (Real.pi / 2)
      linarith [Real.pi_gt_three]

lemma norm_one_add_ew_le [Fact (0 < L)] {w : ℂ} (hw : w ∈ Gamma0 L) : ‖1 + ew L w‖ ≤ M1 := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_one]; unfold M1; linarith [norm_ew_le hw]

lemma norm_one_sub_ew_le [Fact (0 < L)] {w : ℂ} (hw : w ∈ Gamma0 L) : ‖1 - ew L w‖ ≤ M1 := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]; unfold M1; linarith [norm_ew_le hw]

end Contour

/-! ## 3. The quadratic root -/

lemma half_pow_sq (u : ℂ) : ((1 + u) ^ ((2 : ℂ)⁻¹)) ^ 2 = 1 + u := by
  have := Complex.cpow_ofNat_inv_pow (1 + u) 2
  exact_mod_cast this

/-- `aF` solves the quadratic `a² − (1 + e + X) a + e = 0`. -/
theorem aF_quad (L : ℝ) {w : ℂ} (hD : 1 - ew L w ≠ 0) (X : ℂ) :
    aF L w X ^ 2 - (1 + ew L w + X) * aF L w X + ew L w = 0 := by
  have hv := half_pow_sq (uF L w X)
  unfold aF
  unfold uF at hv ⊢
  set v := (1 + (2 * (1 + ew L w) * X + X ^ 2) / (1 - ew L w) ^ 2) ^ ((2 : ℂ)⁻¹)
  have h2 : (1 - ew L w) ^ 2 * v ^ 2 = (1 - ew L w) ^ 2 + 2 * (1 + ew L w) * X + X ^ 2 := by
    rw [hv]; field_simp; ring
  linear_combination h2 / 4

/-- The principal square root has nonnegative real part. -/
lemma re_half_pow_nonneg (x : ℂ) : 0 ≤ (x ^ ((2 : ℂ)⁻¹)).re := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Complex.zero_cpow (by norm_num)]; simp
  rw [Complex.cpow_def_of_ne_zero hx, Complex.exp_re]
  refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
  · have : (log x * (2 : ℂ)⁻¹).im = x.arg / 2 := by
      rw [show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.im_mul_ofReal, log_im]; ring
    rw [this]; linarith [Complex.neg_pi_lt_arg x]
  · have : (log x * (2 : ℂ)⁻¹).im = x.arg / 2 := by
      rw [show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.im_mul_ofReal, log_im]; ring
    rw [this]; linarith [Complex.arg_le_pi x]

/-- `|√(1+u) − 1| ≤ |u|` for the principal root. -/
lemma norm_half_pow_sub_one_le (u : ℂ) : ‖(1 + u) ^ ((2 : ℂ)⁻¹) - 1‖ ≤ ‖u‖ := by
  set v := (1 + u) ^ ((2 : ℂ)⁻¹)
  have hv : v ^ 2 = 1 + u := half_pow_sq u
  have hre : 0 ≤ v.re := re_half_pow_nonneg (1 + u)
  have h1 : 1 ≤ ‖v + 1‖ := by
    have := Complex.abs_re_le_norm (v + 1)
    rw [add_re, one_re] at this
    rw [abs_of_nonneg (by linarith)] at this
    linarith
  have h2 : (v - 1) * (v + 1) = u := by linear_combination hv
  have h3 : ‖v - 1‖ * ‖v + 1‖ = ‖u‖ := by rw [← norm_mul, h2]
  have h4 := norm_nonneg (v - 1)
  nlinarith

section Bounds

variable {L : ℝ} [Fact (0 < L)]

lemma norm_uF_le {w : ℂ} (hw : w ∈ Gamma0 L) {X : ℂ} (hX : ‖X‖ ≤ sig) : ‖uF L w X‖ ≤ 3 / (8 * M1) := by
  have hη := one_sub_ew_lower hw
  have hη0 := etaL_pos
  have hM := M1_ge
  have hs0 := sig_pos
  have hs1 := sig_le
  have hX0 := norm_nonneg X
  have hD0 : 0 < ‖1 - ew L w‖ := lt_of_lt_of_le hη0 hη
  unfold uF
  rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
  have hnum : ‖2 * (1 + ew L w) * X + X ^ 2‖ ≤ 3 * M1 * sig := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat]
    have := norm_one_add_ew_le hw
    have h1 : ‖1 + ew L w‖ * ‖X‖ ≤ M1 * sig :=
      mul_le_mul this hX (norm_nonneg _) (by linarith)
    have h2 : ‖X‖ ^ 2 ≤ sig ^ 2 := pow_le_pow_left₀ hX0 hX 2
    have h3 : sig ^ 2 ≤ M1 * sig := by nlinarith
    nlinarith
  have hsq : etaL ^ 2 ≤ ‖1 - ew L w‖ ^ 2 := pow_le_pow_left₀ hη0.le hη 2
  have e1 : 3 * M1 * sig = 3 / (8 * M1) * etaL ^ 2 := by
    rw [← sig_mul]; field_simp
  calc ‖2 * (1 + ew L w) * X + X ^ 2‖ ≤ 3 * M1 * sig := hnum
    _ = 3 / (8 * M1) * etaL ^ 2 := e1
    _ ≤ 3 / (8 * M1) * ‖1 - ew L w‖ ^ 2 := by gcongr

lemma uF_slit {w : ℂ} (hw : w ∈ Gamma0 L) {X : ℂ} (hX : ‖X‖ ≤ sig) : 1 + uF L w X ∈ slitPlane := by
  have h := norm_uF_le hw hX
  have hM := M1_ge
  have h1 : 3 / (8 * M1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  refine Or.inl ?_
  have := Complex.abs_re_le_norm (uF L w X)
  simp only [add_re, one_re]
  linarith [neg_abs_le (uF L w X).re]

omit [Fact (0 < L)] in
lemma aF_sub_one {w : ℂ} (X : ℂ) :
    aF L w X - 1 = (X + (1 - ew L w) * ((1 + uF L w X) ^ ((2 : ℂ)⁻¹) - 1)) / 2 := by
  unfold aF; ring

lemma norm_aF_sub_one_le {w : ℂ} (hw : w ∈ Gamma0 L) {X : ℂ} (hX : ‖X‖ ≤ sig) :
    ‖aF L w X - 1‖ ≤ 1 / 4 := by
  rw [aF_sub_one, norm_div, Complex.norm_ofNat, div_le_iff₀ (by norm_num)]
  have h1 := norm_uF_le hw hX
  have h2 := norm_half_pow_sub_one_le (uF L w X)
  have h3 := norm_one_sub_ew_le hw
  have hM := M1_ge
  have hs := sig_le
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have h4 : ‖1 - ew L w‖ * ‖(1 + uF L w X) ^ ((2 : ℂ)⁻¹) - 1‖ ≤ M1 * (3 / (8 * M1)) :=
    mul_le_mul h3 (h2.trans h1) (norm_nonneg _) (by positivity)
  have h5 : M1 * (3 / (8 * M1)) = 3 / 8 := by field_simp
  linarith

lemma aF_slit {w : ℂ} (hw : w ∈ Gamma0 L) {X : ℂ} (hX : ‖X‖ ≤ sig) : aF L w X ∈ slitPlane := by
  have h := norm_aF_sub_one_le hw hX
  refine Or.inl ?_
  have := Complex.abs_re_le_norm (aF L w X - 1)
  have e : (aF L w X).re = 1 + (aF L w X - 1).re := by simp
  rw [e]; linarith [neg_abs_le (aF L w X - 1).re]

lemma norm_FW_le {w : ℂ} (hw : w ∈ Gamma0 L) {X : ℂ} (hX : ‖X‖ ≤ sig) : ‖FW L w X‖ ≤ 1 := by
  have h := norm_aF_sub_one_le hw hX
  have h2 := Complex.norm_log_one_add_half_le_self (z := aF L w X - 1) (by linarith)
  rw [add_sub_cancel] at h2
  unfold FW; linarith

lemma hasDerivAt_aF_inner (L : ℝ) (w X : ℂ) :
    HasDerivAt (fun Y => 1 + uF L w Y)
      ((2 * (1 + ew L w) + 2 * X) / (1 - ew L w) ^ 2) X := by
  have h1 : HasDerivAt (fun Y : ℂ => 2 * (1 + ew L w) * Y) (2 * (1 + ew L w)) X := by
    simpa using (hasDerivAt_id' X).const_mul (2 * (1 + ew L w))
  have h2 : HasDerivAt (fun Y : ℂ => Y ^ 2) (2 * X) X := by simpa using hasDerivAt_pow 2 X
  exact ((h1.add h2).div_const ((1 - ew L w) ^ 2)).const_add 1

lemma differentiableAt_FW {w : ℂ} (hw : w ∈ Gamma0 L) {X : ℂ} (hX : ‖X‖ ≤ sig) :
    DifferentiableAt ℂ (FW L w) X := by
  have hin := (hasDerivAt_aF_inner L w X).differentiableAt
  have hcp : DifferentiableAt ℂ (fun Y => (1 + uF L w Y) ^ ((2 : ℂ)⁻¹)) X :=
    hin.cpow (differentiableAt_const _) (uF_slit hw hX)
  have ha : DifferentiableAt ℂ (aF L w) X := by
    have : aF L w = fun Y => (1 + ew L w + Y + (1 - ew L w) * (1 + uF L w Y) ^ ((2 : ℂ)⁻¹)) / 2 :=
      rfl
    rw [this]
    exact (((differentiableAt_const _).add differentiableAt_id).add
      ((differentiableAt_const _).mul hcp)).div_const 2
  exact ha.clog (aF_slit hw hX)

end Bounds

/-! ## 4. The expansion -/

lemma aF_zero (L : ℝ) (w : ℂ) : aF L w 0 = 1 := by
  unfold aF uF
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero, Complex.one_cpow, mul_one]
  ring

lemma hasDerivAt_FW_zero (L : ℝ) {w : ℂ} (hD : 1 - ew L w ≠ 0) :
    HasDerivAt (FW L w) (1 / (1 - ew L w)) 0 := by
  have h1 := hasDerivAt_aF_inner L w 0
  have hu0 : 1 + uF L w 0 = 1 := by unfold uF; simp
  have hslit : 1 + uF L w 0 ∈ slitPlane := by rw [hu0]; exact one_mem_slitPlane
  have h2 := h1.cpow_const (c := (2 : ℂ)⁻¹) hslit
  have h3 := (((hasDerivAt_const (0 : ℂ) (1 + ew L w)).add (hasDerivAt_id (0 : ℂ))).add
    (h2.const_mul (1 - ew L w))).div_const 2
  have ha0 := aF_zero L w
  have hslit2 : aF L w 0 ∈ slitPlane := by rw [ha0]; exact one_mem_slitPlane
  have h4 := h3.clog (f := aF L w) hslit2
  refine h4.congr_deriv ?_
  rw [ha0, hu0, Complex.one_cpow]
  field_simp
  ring

/-- **`QG:eq:haar-free-taylor`.** There are a radius `σ > 0` and `M ≥ 0`, depending only on `L`, such that for
every `w ∈ Γ_0`: `F_w` is holomorphic on `|X| ≤ σ`, the quadratic root `aF` stays within `1/4` of `1` there,
and `F_w(X) = Σ_d f_d X^d` (`|X| < σ`) with `f_0 = 0`, `f_1 = (1 − e^{iwL})^{-1}`, `|f_d| ≤ M σ^{-d}`. -/
theorem free_taylor (L : ℝ) [Fact (0 < L)] :
    ∃ σ M : ℝ, 0 < σ ∧ 0 ≤ M ∧ σ = sig ∧ ∀ w ∈ Gamma0 L,
      1 - ew L w ≠ 0 ∧
      DifferentiableOn ℂ (FW L w) (closedBall 0 σ) ∧
      (∀ X, ‖X‖ ≤ σ → ‖aF L w X - 1‖ ≤ 1 / 4) ∧
      ∃ f : ℕ → ℂ, f 0 = 0 ∧ f 1 = 1 / (1 - ew L w) ∧ (∀ d, ‖f d‖ ≤ M * σ⁻¹ ^ d) ∧
        ∀ X, ‖X‖ < σ → HasSum (fun d => f d * X ^ d) (FW L w X) := by
  refine ⟨sig, 1, sig_pos, zero_le_one, rfl, fun w hw => ?_⟩
  have hD : 1 - ew L w ≠ 0 := by
    intro h0
    have := one_sub_ew_lower hw
    rw [h0, norm_zero] at this; linarith [etaL_pos]
  have hdiff : DifferentiableOn ℂ (FW L w) (closedBall 0 sig) := fun X hX =>
    (differentiableAt_FW hw (by simpa using hX)).differentiableWithinAt
  refine ⟨hD, hdiff, fun X hX => norm_aF_sub_one_le hw hX, ?_⟩
  set R : NNReal := Real.toNNReal sig with hR
  have hRv : (R : ℝ) = sig := Real.coe_toNNReal _ sig_pos.le
  have hRpos : 0 < R := by rw [← NNReal.coe_pos, hRv]; exact sig_pos
  have hps := (show DifferentiableOn ℂ (FW L w) (closedBall 0 (R : ℝ)) by rw [hRv]; exact hdiff).hasFPowerSeriesOnBall
    hRpos
  set p := cauchyPowerSeries (FW L w) 0 (R : ℝ) with hp
  refine ⟨fun d => p.coeff d, ?_, ?_, ?_, ?_⟩
  · -- f_0 = F_w(0) = log 1
    have := hps.hasFPowerSeriesAt.coeff_zero (fun _ => 1)
    rw [FW, aF_zero L w, log_one] at this
    show p.coeff 0 = 0
    unfold FormalMultilinearSeries.coeff
    exact this
  · -- f_1 = F_w'(0)
    have h1 := hps.hasFPowerSeriesAt.deriv
    rw [(hasDerivAt_FW_zero L hD).deriv] at h1
    show p.coeff 1 = _
    rw [h1]; rfl
  · -- Cauchy bound
    intro d
    rw [← FormalMultilinearSeries.norm_apply_eq_norm_coef]
    refine (norm_cauchyPowerSeries_le _ _ _ _).trans ?_
    have hint : ∫ θ in (0 : ℝ)..2 * Real.pi, ‖FW L w (circleMap 0 (R : ℝ) θ)‖ ≤
        ∫ θ in (0 : ℝ)..2 * Real.pi, (1 : ℝ) := by
      refine intervalIntegral.integral_mono_on (by positivity) ?_ (by simp) fun θ _ => ?_
      · refine ContinuousOn.intervalIntegrable fun θ _ => ?_
        have hX : ‖circleMap 0 (R : ℝ) θ‖ ≤ sig := by
          rw [norm_circleMap_zero, hRv, abs_of_pos sig_pos]
        exact ((differentiableAt_FW hw hX).continuousAt.comp
          (continuous_circleMap 0 _).continuousAt).norm.continuousWithinAt
      · have hX : ‖circleMap 0 (R : ℝ) θ‖ ≤ sig := by
          rw [norm_circleMap_zero, hRv, abs_of_pos sig_pos]
        exact norm_FW_le hw hX
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at hint
    have hRr : |(R : ℝ)| = sig := by rw [hRv, abs_of_pos sig_pos]
    rw [hRr]
    calc ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖FW L w (circleMap 0 (R : ℝ) θ)‖) *
          sig⁻¹ ^ d ≤ ((2 * Real.pi)⁻¹ * (2 * Real.pi)) * sig⁻¹ ^ d :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hint (by positivity))
            (pow_nonneg (inv_nonneg.2 sig_pos.le) d)
      _ = 1 * sig⁻¹ ^ d := by rw [inv_mul_cancel₀ (by positivity)]
  · -- the expansion
    intro X hX
    have hXR : ‖X‖ < (R : ℝ) := by rw [hRv]; exact hX
    have hXb : X ∈ Metric.eball (0 : ℂ) (R : ENNReal) := by
      simpa [Metric.mem_eball, edist_zero_right] using hXR
    have := hps.hasSum hXb
    rw [zero_add] at this
    refine this.congr_fun fun d => ?_
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_comm]

end QuantumNLS.HaarFreeTaylor

#print axioms QuantumNLS.HaarFreeTaylor.aF_quad
#print axioms QuantumNLS.HaarFreeTaylor.one_sub_ew_lower
#print axioms QuantumNLS.HaarFreeTaylor.free_taylor
