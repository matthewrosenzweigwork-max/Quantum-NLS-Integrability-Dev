import Mathlib

/-! LOCAL-007 stage F: elementary complex analysis for the quadratic factor (no argument principle).

* `factor_exists`: an entire `f` vanishing at `α ± t` (and with `f'(α)=0` if `t=0`) factors as
  `f = ((z-α)²-t²) H` with `H` entire (two applications of `dslope`);
* `H_real`: `H` is real on the real axis when `f` is;
* `sinc`, `H0`: the free factor `H0(z) = -L² sinc(Lz/2)²` with `4cos²(Lz/2)-4 = z² H0(z)`;
* `H_close`: closeness of `f` to `f0` on `|ξ| = 3d` and smallness of `|α|+t` give `|H + L²| ≤ L²/4`
  on the closed disc (maximum modulus). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set Filter Topology Metric
namespace QuantumNLS.Local007Factor

/-! ### The factorization -/

theorem factor_exists {f : ℂ → ℂ} (hf : Differentiable ℂ f) (α t : ℝ) (ht : 0 ≤ t)
    (h1 : f ((α : ℂ) + t) = 0) (h2 : f ((α : ℂ) - t) = 0) (h3 : t = 0 → deriv f (α : ℂ) = 0) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ z, f z = ((z - α) ^ 2 - (t : ℂ) ^ 2) * H z := by
  set r1 : ℂ := (α : ℂ) + t with hr1
  set r2 : ℂ := (α : ℂ) - t with hr2
  have hd1 : Differentiable ℂ (dslope f r1) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope (s := univ) univ_mem]
    exact hf.differentiableOn
  have h12 : dslope f r1 r2 = 0 := by
    by_cases ht0 : t = 0
    · have e1 : r2 = r1 := by simp [hr1, hr2, ht0]
      rw [e1, dslope_same]
      have : (α : ℂ) = r1 := by simp [hr1, ht0]
      rw [← this]; exact h3 ht0
    · have hne : r2 ≠ r1 := by
        intro he
        apply ht0
        have : (t : ℂ) = 0 := by
          have h' : (α : ℂ) - t = (α : ℂ) + t := he
          have : (2 : ℂ) * t = 0 := by linear_combination h'.symm
          simpa using this
        exact_mod_cast this
      rw [dslope_of_ne _ hne, slope_def_field, h2, h1]; simp
  have hd2 : Differentiable ℂ (dslope (dslope f r1) r2) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope (s := univ) univ_mem]
    exact hd1.differentiableOn
  refine ⟨dslope (dslope f r1) r2, hd2, fun z => ?_⟩
  have e1 := sub_smul_dslope f r1 z
  have e2 := sub_smul_dslope (dslope f r1) r2 z
  simp only [smul_eq_mul, h1, h12, sub_zero] at e1 e2
  have : ((z - α) ^ 2 - (t : ℂ) ^ 2) = (z - r1) * (z - r2) := by simp only [hr1, hr2]; ring
  rw [this, mul_assoc, e2, e1]

theorem H_real {f H : ℂ → ℂ} (hH : Differentiable ℂ H) (α t : ℝ)
    (hfH : ∀ z, f z = ((z - α) ^ 2 - (t : ℂ) ^ 2) * H z) (hfr : ∀ x : ℝ, (f x).im = 0) (x : ℝ) :
    (H x).im = 0 := by
  have hc : Continuous fun y : ℝ => (H (y : ℂ)).im :=
    Complex.continuous_im.comp (hH.continuous.comp Complex.continuous_ofReal)
  have hdense : Dense {y : ℝ | y ≠ α + t ∧ y ≠ α - t} := by
    have : {y : ℝ | y ≠ α + t ∧ y ≠ α - t} = ({α + t, α - t} : Set ℝ)ᶜ := by
      ext y; simp [not_or]
    rw [this]
    exact ((Set.toFinite _).countable).dense_compl ℝ
  have hz : ∀ y ∈ {y : ℝ | y ≠ α + t ∧ y ≠ α - t}, (H (y : ℂ)).im = 0 := by
    rintro y ⟨hy1, hy2⟩
    have hP : ((y : ℂ) - α) ^ 2 - (t : ℂ) ^ 2 = (((y - α) ^ 2 - t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have hne : (y - α) ^ 2 - t ^ 2 ≠ 0 := by
      intro h
      have : (y - α - t) * (y - α + t) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h | h
      · exact hy1 (by linarith)
      · exact hy2 (by linarith)
    have hfy : f (y : ℂ) = (((y - α) ^ 2 - t ^ 2 : ℝ) : ℂ) * H (y : ℂ) := by rw [hfH, hP]
    have hHx : H (y : ℂ) = f y / (((y - α) ^ 2 - t ^ 2 : ℝ) : ℂ) := by
      rw [hfy, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.2 hne)]
    rw [hHx, Complex.div_ofReal_im, hfr, zero_div]
  have := hc.ext_on hdense continuous_const hz
  exact congrFun this x

/-! ### The free factor -/

/-- `sinc w = sin w / w` (value `1` at `0`). -/
def sinc : ℂ → ℂ := dslope Complex.sin 0

theorem sinc_mul (w : ℂ) : sinc w * w = Complex.sin w := by
  have := sub_smul_dslope Complex.sin 0 w
  simp only [smul_eq_mul, sub_zero, Complex.sin_zero] at this
  rw [mul_comm]; exact this

theorem differentiable_sinc : Differentiable ℂ sinc := by
  show Differentiable ℂ (dslope Complex.sin 0)
  rw [← differentiableOn_univ, Complex.differentiableOn_dslope (s := univ) univ_mem]
  exact Complex.differentiable_sin.differentiableOn

theorem sinc_zero : sinc 0 = 1 := by
  rw [sinc, dslope_same]; simp

theorem norm_sinc_sub_one {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖sinc w - 1‖ ≤ ‖w‖ ^ 2 / 5 := by
  by_cases h0 : w = 0
  · subst h0; simp [sinc_zero]
  have hb := Complex.sin_bound hw
  have hs : sinc w = Complex.sin w / w := by rw [eq_div_iff h0]; exact sinc_mul w
  have e : sinc w - 1 = -w ^ 2 / 6 + (Complex.sin w - (w - w ^ 3 / 6)) / w := by
    rw [hs]; field_simp; ring
  rw [e]
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 h0
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖-w ^ 2 / 6‖ = ‖w‖ ^ 2 / 6 := by rw [norm_div, norm_neg, norm_pow]; norm_num
  have h2 : ‖(Complex.sin w - (w - w ^ 3 / 6)) / w‖ ≤ ‖w‖ ^ 4 / 100 := by
    rw [norm_div, div_le_iff₀ hwn]
    calc ‖Complex.sin w - (w - w ^ 3 / 6)‖ ≤ ‖w‖ ^ 5 / 100 := hb
      _ = ‖w‖ ^ 4 / 100 * ‖w‖ := by ring
  rw [h1]
  have : ‖w‖ ^ 4 ≤ ‖w‖ ^ 2 := pow_le_pow_of_le_one hwn.le hw (by norm_num)
  nlinarith

/-- The free quadratic cofactor `H0(z) = -L² sinc(Lz/2)²`. -/
def H0 (L : ℝ) (z : ℂ) : ℂ := -(L : ℂ) ^ 2 * sinc ((L : ℂ) * z / 2) ^ 2

theorem differentiable_H0 (L : ℝ) : Differentiable ℂ (H0 L) := by
  unfold H0
  exact (differentiable_const _).mul
    ((differentiable_sinc.comp ((differentiable_const _).mul differentiable_id |>.div_const 2)).pow 2)

theorem f0_eq (L : ℝ) (z : ℂ) :
    (2 * Complex.cos ((L : ℂ) * z / 2)) ^ 2 - 4 = z ^ 2 * H0 L z := by
  unfold H0
  have h := sinc_mul ((L : ℂ) * z / 2)
  have hs := Complex.sin_sq_add_cos_sq ((L : ℂ) * z / 2)
  rw [← h] at hs
  have : (2 * Complex.cos ((L : ℂ) * z / 2)) ^ 2 - 4 =
      -4 * (sinc ((L : ℂ) * z / 2) * ((L : ℂ) * z / 2)) ^ 2 := by
    linear_combination 4 * hs
  rw [this]; ring

theorem norm_H0_add {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : ‖z‖ ≤ 1 / (4 * L)) :
    ‖H0 L z + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 100 := by
  have hw : ‖(L : ℂ) * z / 2‖ ≤ 1 / 8 := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hL.le, Complex.norm_two]
    have : L * ‖z‖ ≤ 1 / 4 := by
      calc L * ‖z‖ ≤ L * (1 / (4 * L)) := by gcongr
        _ = 1 / 4 := by field_simp
    linarith
  have h1 := norm_sinc_sub_one (hw.trans (by norm_num))
  set s := sinc ((L : ℂ) * z / 2)
  have hn : ‖(L : ℂ) * z / 2‖ ^ 2 / 5 ≤ 1 / 320 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hw 2
    nlinarith
  have hs1 : ‖s - 1‖ ≤ 1 / 320 := h1.trans hn
  have e : H0 L z + (L : ℂ) ^ 2 = -(L : ℂ) ^ 2 * ((s - 1) * (s + 1)) := by
    unfold H0; ring
  rw [e, norm_mul, norm_mul]
  have hs2 : ‖s + 1‖ ≤ 3 := by
    have : ‖s + 1‖ ≤ ‖s - 1‖ + ‖(2 : ℂ)‖ := by
      calc ‖s + 1‖ = ‖(s - 1) + 2‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    rw [Complex.norm_two] at this; linarith
  have hL2 : ‖-(L : ℂ) ^ 2‖ = L ^ 2 := by
    rw [norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg hL.le]
  rw [hL2]
  calc L ^ 2 * (‖s - 1‖ * ‖s + 1‖) ≤ L ^ 2 * (1 / 320 * 3) := by gcongr
    _ ≤ L ^ 2 / 100 := by nlinarith [sq_nonneg L]

/-! ### Closeness of the actual cofactor on the disc -/

theorem H_close {L : ℝ} (hL : 0 < L) {d : ℝ} (hd : d = 1 / (16 * L)) {f H : ℂ → ℂ}
    (hH : Differentiable ℂ H) {α t : ℝ} (ht : 0 ≤ t) (hδ : |α| + t ≤ d / 40)
    (hfH : ∀ z, f z = ((z - α) ^ 2 - (t : ℂ) ^ 2) * H z)
    (hfc : ∀ ξ : ℂ, ‖ξ‖ = 3 * d → ‖f ξ - (2 * Complex.cos ((L : ℂ) * ξ / 2)) ^ 2 + 4‖ ≤ L ^ 2 * d ^ 2 / 20) :
    ∀ z : ℂ, ‖z‖ ≤ 3 * d → ‖H z + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 4 := by
  have hd0 : 0 < d := by rw [hd]; positivity
  have hLd : L * d = 1 / 16 := by rw [hd]; field_simp
  have hL2d2 : L ^ 2 * d ^ 2 = 1 / 256 := by
    have : L ^ 2 * d ^ 2 = (L * d) ^ 2 := by ring
    rw [this, hLd]; norm_num
  -- on the circle
  have hcirc : ∀ ξ : ℂ, ‖ξ‖ = 3 * d → ‖H ξ - H0 L ξ‖ ≤ L ^ 2 * (1 / 10) := by
    intro ξ hξ
    have hξ0 : ξ ≠ 0 := by intro h; rw [h, norm_zero] at hξ; linarith
    set P : ℂ := (ξ - α) ^ 2 - (t : ℂ) ^ 2 with hP
    have hα : |α| ≤ d / 40 := by have := abs_nonneg α; linarith
    have hαn : ‖(α : ℂ)‖ ≤ d / 40 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hα
    have htn : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg ht]
    have hPq : ‖P - ξ ^ 2‖ ≤ (4 / 25) * d ^ 2 := by
      have e : P - ξ ^ 2 = -2 * α * ξ + (α : ℂ) ^ 2 - (t : ℂ) ^ 2 := by rw [hP]; ring
      rw [e]
      have h1 : ‖-2 * (α : ℂ) * ξ‖ ≤ 2 * (d / 40) * (3 * d) := by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_two, hξ]
        gcongr
      have h2 : ‖(α : ℂ) ^ 2 - (t : ℂ) ^ 2‖ ≤ (d / 40) ^ 2 := by
        have ha : |α| ^ 2 ≤ (d / 40) ^ 2 := by
          have : |α| ≤ d / 40 := hα
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
        have : ‖(α : ℂ) ^ 2 - (t : ℂ) ^ 2‖ ≤ α ^ 2 + t ^ 2 := by
          calc ‖(α : ℂ) ^ 2 - (t : ℂ) ^ 2‖ ≤ ‖(α : ℂ) ^ 2‖ + ‖(t : ℂ) ^ 2‖ := norm_sub_le _ _
            _ = α ^ 2 + t ^ 2 := by
              rw [norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                Real.norm_eq_abs, sq_abs, sq_abs]
        have h3 : α ^ 2 + t ^ 2 ≤ (|α| + t) ^ 2 := by nlinarith [abs_nonneg α, sq_abs α]
        have h4 : (|α| + t) ^ 2 ≤ (d / 40) ^ 2 := pow_le_pow_left₀ (by positivity) hδ 2
        linarith
      have := norm_add_le (-2 * (α : ℂ) * ξ + (α : ℂ) ^ 2) (-(t : ℂ) ^ 2)
      calc ‖-2 * (α : ℂ) * ξ + (α : ℂ) ^ 2 - (t : ℂ) ^ 2‖
          = ‖-2 * (α : ℂ) * ξ + ((α : ℂ) ^ 2 - (t : ℂ) ^ 2)‖ := by ring_nf
        _ ≤ ‖-2 * (α : ℂ) * ξ‖ + ‖(α : ℂ) ^ 2 - (t : ℂ) ^ 2‖ := norm_add_le _ _
        _ ≤ 2 * (d / 40) * (3 * d) + (d / 40) ^ 2 := add_le_add h1 h2
        _ ≤ (4 / 25) * d ^ 2 := by nlinarith [sq_nonneg d]
    have hq : ‖ξ ^ 2‖ = 9 * d ^ 2 := by rw [norm_pow, hξ]; ring
    have hPn : (44 / 5) * d ^ 2 ≤ ‖P‖ := by
      have h1 : ‖ξ ^ 2 - P‖ ≤ (4 / 25) * d ^ 2 := by rw [norm_sub_rev]; exact hPq
      have := norm_sub_norm_le (ξ ^ 2) P
      nlinarith [sq_nonneg d]
    have hP0 : P ≠ 0 := by
      intro h; rw [h, norm_zero] at hPn; nlinarith [sq_nonneg d]
    have hHξ : H ξ = f ξ / P := by
      rw [hfH ξ, mul_div_cancel_left₀ _ hP0]
    have hξL : ‖ξ‖ ≤ 1 / (4 * L) := by
      rw [hξ, hd]; rw [show 3 * (1 / (16 * L)) = 3 / (16 * L) by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    set F0 : ℂ := (2 * Complex.cos ((L : ℂ) * ξ / 2)) ^ 2 - 4 with hF0
    have hF0e : F0 = ξ ^ 2 * H0 L ξ := f0_eq L ξ
    have e : H ξ - H0 L ξ = (f ξ - F0) / P + H0 L ξ * (ξ ^ 2 - P) / P := by
      rw [hHξ, hF0e]; field_simp; ring
    have hPpos : 0 < ‖P‖ := lt_of_lt_of_le (by positivity) hPn
    have hH0n : ‖H0 L ξ‖ ≤ (101 / 100) * L ^ 2 := by
      have h1 := norm_H0_add hL hξL
      have h2 : ‖(L : ℂ) ^ 2‖ = L ^ 2 := by
        rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hL.le]
      have h3 : ‖H0 L ξ‖ ≤ ‖H0 L ξ + (L : ℂ) ^ 2‖ + ‖(L : ℂ) ^ 2‖ := by
        calc ‖H0 L ξ‖ = ‖(H0 L ξ + (L : ℂ) ^ 2) - (L : ℂ) ^ 2‖ := by rw [add_sub_cancel_right]
          _ ≤ _ := norm_sub_le _ _
      rw [h2] at h3; linarith
    have hT1 : ‖(f ξ - F0) / P‖ ≤ L ^ 2 / 150 := by
      rw [norm_div, div_le_iff₀ hPpos]
      have h1 : ‖f ξ - F0‖ ≤ L ^ 2 * d ^ 2 / 20 := by
        have := hfc ξ hξ
        have e2 : f ξ - (2 * Complex.cos ((L : ℂ) * ξ / 2)) ^ 2 + 4 = f ξ - F0 := by rw [hF0]; ring
        rwa [e2] at this
      nlinarith [mul_nonneg (sq_nonneg L) (sub_nonneg.2 hPn), mul_nonneg (sq_nonneg L) (sq_nonneg d)]
    have hT2 : ‖H0 L ξ * (ξ ^ 2 - P) / P‖ ≤ L ^ 2 / 50 := by
      rw [norm_div, norm_mul, div_le_iff₀ hPpos]
      have h1 : ‖ξ ^ 2 - P‖ ≤ (4 / 25) * d ^ 2 := by rw [norm_sub_rev]; exact hPq
      calc ‖H0 L ξ‖ * ‖ξ ^ 2 - P‖ ≤ ((101 / 100) * L ^ 2) * ((4 / 25) * d ^ 2) := by
            gcongr
        _ ≤ L ^ 2 / 50 * ‖P‖ := by
            nlinarith [mul_nonneg (sq_nonneg L) (sub_nonneg.2 hPn), mul_nonneg (sq_nonneg L) (sq_nonneg d)]
    rw [e]
    calc ‖(f ξ - F0) / P + H0 L ξ * (ξ ^ 2 - P) / P‖ ≤ L ^ 2 / 150 + L ^ 2 / 50 :=
          (norm_add_le _ _).trans (add_le_add hT1 hT2)
      _ ≤ L ^ 2 * (1 / 10) := by nlinarith [sq_nonneg L]
  intro z hz
  have hdc : DiffContOnCl ℂ (fun w => H w - H0 L w) (ball (0 : ℂ) (3 * d)) :=
    (hH.sub (differentiable_H0 L)).diffContOnCl
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball) hdc
    (C := L ^ 2 * (1 / 10))
    (fun w hw => by
      rw [frontier_ball (0 : ℂ) (by positivity : (3 * d) ≠ 0)] at hw
      exact hcirc w (by simpa using hw))
    (z := z) (by rw [closure_ball (0 : ℂ) (by positivity : (3 * d) ≠ 0)]; simpa using hz)
  have hzL : ‖z‖ ≤ 1 / (4 * L) := by
    refine hz.trans ?_
    rw [hd, show 3 * (1 / (16 * L)) = 3 / (16 * L) by ring, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc ‖H z + (L : ℂ) ^ 2‖ = ‖(H z - H0 L z) + (H0 L z + (L : ℂ) ^ 2)‖ := by ring_nf
    _ ≤ ‖H z - H0 L z‖ + ‖H0 L z + (L : ℂ) ^ 2‖ := norm_add_le _ _
    _ ≤ L ^ 2 * (1 / 10) + L ^ 2 / 100 := add_le_add hmax (norm_H0_add hL hzL)
    _ ≤ L ^ 2 / 4 := by nlinarith [sq_nonneg L]

end QuantumNLS.Local007Factor
#print axioms QuantumNLS.Local007Factor.factor_exists
#print axioms QuantumNLS.Local007Factor.H_real
#print axioms QuantumNLS.Local007Factor.H_close
