import Mathlib

/-!
# R-8F7E0394 (`CC:F03:deterministic`), stage (G), part 1: the truncated coefficients `a_{m,N}`

Source (F03.tex, proof of `CC:F03:deterministic`, "weak lower bound"): "Choose continuous functions `0 ≤ χ_m ≤ 1` of a real variable, zero when `|r| ≤ 1/(2m)`, one when `|r| ≥ 1/m`, and increasing in `m` at every fixed `r`.
Put `a_{m,N}(t,s) = √χ_m(Q_N(t)-Q_N(s)) / √(c_N² + (Q_N(t)-Q_N(s))²)`. These symmetric coefficients are bounded by `2m` and converge almost everywhere to
`a_m = √χ_m(Q(t)-Q(s))/|Q(t)-Q(s)|`, with zero assigned when its numerator vanishes."

Here `chi m r = min 1 (max 0 (2m|r| - 1))` and `coef m c x y = √χ_m(x-y)/√(c²+(x-y)²)` (so `a_{m,N}(t,s) = coef m c_N (Q_N t) (Q_N s)` and `a_m = coef m 0 (Q t) (Q s)`, `0` when `Q t = Q s` as `χ_m(0) = 0`).
-/

set_option autoImplicit false

open Filter Topology

noncomputable section

namespace QuantumNLS.GLowerKernel

/-- `χ_m(r) = min 1 (max 0 (2m|r| - 1))`: continuous, `0 ≤ χ_m ≤ 1`, zero for `|r| ≤ 1/(2m)`, one for `|r| ≥ 1/m`. -/
def chi (m r : ℝ) : ℝ := min 1 (max 0 (2 * m * |r| - 1))

theorem chi_nonneg (m r : ℝ) : 0 ≤ chi m r := le_min zero_le_one (le_max_left _ _)

theorem chi_le_one (m r : ℝ) : chi m r ≤ 1 := min_le_left _ _

theorem chi_zero_of_le {m r : ℝ} (hm : 0 < m) (h : |r| ≤ 1 / (2 * m)) : chi m r = 0 := by
  unfold chi
  have h1 : 2 * m * |r| ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * m)
    rwa [mul_one_div_cancel (by positivity)] at this
  rw [max_eq_left (by linarith)]
  exact min_eq_right zero_le_one

theorem chi_one_of_ge {m r : ℝ} (hm : 0 < m) (h : 1 / m ≤ |r|) : chi m r = 1 := by
  unfold chi
  have h1 : 1 ≤ m * |r| := by
    have := mul_le_mul_of_nonneg_left h hm.le
    rwa [mul_one_div_cancel hm.ne'] at this
  rw [max_eq_right (by linarith)]
  exact min_eq_left (by linarith)

theorem chi_mono {m m' : ℝ} (hm : 0 ≤ m) (h : m ≤ m') (r : ℝ) : chi m r ≤ chi m' r := by
  unfold chi
  have := abs_nonneg r
  exact min_le_min le_rfl (max_le_max le_rfl (by nlinarith))

theorem continuous_chi (m : ℝ) : Continuous (chi m) := by
  unfold chi
  exact continuous_const.min (continuous_const.max
    ((continuous_const.mul continuous_abs).sub continuous_const))

theorem chi_zero (m : ℝ) : chi m 0 = 0 := by
  simp [chi]

/-- `a_{m,N}(t,s) = coef m c_N (Q_N t) (Q_N s)`. -/
def coef (m c x y : ℝ) : ℝ := Real.sqrt (chi m (x - y)) / Real.sqrt (c ^ 2 + (x - y) ^ 2)

theorem coef_nonneg (m c x y : ℝ) : 0 ≤ coef m c x y :=
  div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem coef_symm (m c x y : ℝ) : coef m c x y = coef m c y x := by
  have h1 : chi m (x - y) = chi m (y - x) := by
    unfold chi; rw [abs_sub_comm]
  have h2 : (x - y) ^ 2 = (y - x) ^ 2 := by ring
  unfold coef
  rw [h1, h2]

/-- The coefficients are bounded by `2m`. -/
theorem coef_le {m : ℝ} (hm : 0 < m) (c x y : ℝ) : coef m c x y ≤ 2 * m := by
  by_cases h : |x - y| ≤ 1 / (2 * m)
  · unfold coef
    rw [chi_zero_of_le hm h]
    simp; positivity
  · push_neg at h
    have hd : 1 / (2 * m) ≤ Real.sqrt (c ^ 2 + (x - y) ^ 2) :=
      h.le.trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg c]))
    have hpos : 0 < Real.sqrt (c ^ 2 + (x - y) ^ 2) :=
      lt_of_lt_of_le (by positivity) hd
    unfold coef
    rw [div_le_iff₀ hpos]
    have h1 : Real.sqrt (chi m (x - y)) ≤ 1 := by
      rw [Real.sqrt_le_one]; exact chi_le_one _ _
    have h2 : 1 ≤ 2 * m * Real.sqrt (c ^ 2 + (x - y) ^ 2) := by
      have := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2 * m)
      rwa [mul_one_div_cancel (by positivity)] at this
    linarith

/-- `a_{m,N}² ≤ 1/(c² + (x-y)²)`. -/
theorem coef_sq_le (m c x y : ℝ) : coef m c x y ^ 2 ≤ 1 / (c ^ 2 + (x - y) ^ 2) := by
  unfold coef
  have hd : 0 ≤ c ^ 2 + (x - y) ^ 2 := by positivity
  rw [div_pow, Real.sq_sqrt (chi_nonneg _ _), Real.sq_sqrt hd]
  exact div_le_div_of_nonneg_right (chi_le_one _ _) hd

theorem coef_mono {m m' : ℝ} (hm : 0 ≤ m) (h : m ≤ m') (c x y : ℝ) : coef m c x y ≤ coef m' c x y := by
  unfold coef
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (chi_mono hm h _)) (Real.sqrt_nonneg _)

theorem coef_zero_of_eq (m c x : ℝ) : coef m c x x = 0 := by
  simp [coef, chi_zero]

/-- The a.e. limit: `a_{m,N} → a_m` where `Q_N → Q`, `c_N → 0`. -/
theorem tendsto_coef {m : ℝ} (hm : 0 < m) {c : ℕ → ℝ} {x y : ℕ → ℝ} {x0 y0 : ℝ}
    (hc : Tendsto c atTop (𝓝 0)) (hx : Tendsto x atTop (𝓝 x0)) (hy : Tendsto y atTop (𝓝 y0)) :
    Tendsto (fun n => coef m (c n) (x n) (y n)) atTop (𝓝 (coef m 0 x0 y0)) := by
  by_cases h : x0 = y0
  · subst h
    rw [coef_zero_of_eq]
    have hd : Tendsto (fun n => x n - y n) atTop (𝓝 0) := by simpa using hx.sub hy
    have habs : Tendsto (fun n => |x n - y n|) atTop (𝓝 0) := by simpa using hd.abs
    have hev : ∀ᶠ n in atTop, |x n - y n| < 1 / (2 * m) :=
      habs.eventually (gt_mem_nhds (by positivity))
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev] with n hn
    unfold coef
    rw [chi_zero_of_le hm hn.le]
    simp
  · have hne : x0 - y0 ≠ 0 := sub_ne_zero.2 h
    have hg : ContinuousAt (fun z : ℝ × ℝ × ℝ => coef m z.1 z.2.1 z.2.2) (0, x0, y0) := by
      unfold coef
      apply ContinuousAt.div
      · exact (Real.continuous_sqrt.comp ((continuous_chi m).comp
          (continuous_snd.fst.sub continuous_snd.snd))).continuousAt
      · exact (Real.continuous_sqrt.comp ((continuous_fst.pow 2).add
          ((continuous_snd.fst.sub continuous_snd.snd).pow 2))).continuousAt
      · have hpos : 0 < (0 : ℝ) ^ 2 + (x0 - y0) ^ 2 := by
          have : 0 < (x0 - y0) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
          linarith
        exact (Real.sqrt_pos.2 hpos).ne'
    have hseq : Tendsto (fun n => (c n, x n, y n)) atTop (𝓝 ((0 : ℝ), x0, y0)) :=
      hc.prodMk_nhds (hx.prodMk_nhds hy)
    have key := hg.tendsto.comp hseq
    exact key

/-- Monotone limit in `m`: for `x ≠ y`, `coef m 0 x y ^ 2 = 1/(x-y)^2` once `m ≥ 1/|x-y|`. -/
theorem coef_sq_eventually {x y : ℝ} (h : x ≠ y) :
    ∀ᶠ m : ℕ in atTop, coef ((m : ℝ) + 1) 0 x y ^ 2 = 1 / (x - y) ^ 2 := by
  have hne : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 h)
  obtain ⟨M, hM⟩ := exists_nat_ge (1 / |x - y|)
  filter_upwards [eventually_ge_atTop M] with m hm
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h1 : 1 / ((m : ℝ) + 1) ≤ |x - y| := by
    rw [div_le_iff₀ hm1]
    have : (M : ℝ) ≤ m := by exact_mod_cast hm
    have h2 : 1 ≤ (M : ℝ) * |x - y| := by
      have := mul_le_mul_of_nonneg_right hM hne.le
      rwa [one_div, inv_mul_cancel₀ hne.ne'] at this
    nlinarith
  unfold coef
  rw [chi_one_of_ge hm1 h1, div_pow, Real.sq_sqrt zero_le_one, Real.sq_sqrt (by positivity)]
  simp

end QuantumNLS.GLowerKernel

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.GLowerKernel.coef_le
#print axioms QuantumNLS.GLowerKernel.coef_sq_le
#print axioms QuantumNLS.GLowerKernel.tendsto_coef
#print axioms QuantumNLS.GLowerKernel.coef_sq_eventually
