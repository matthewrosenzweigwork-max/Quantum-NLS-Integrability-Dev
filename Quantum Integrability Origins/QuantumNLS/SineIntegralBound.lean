import Mathlib

/-!
# R-064239ED: uniform bounds for truncated sine integrals

`B(c;a,b) = ∫_a^b sin(ct)/t dt`, `0 < a ≤ b`, `c ∈ ℝ`:
* `sine_integral_le_four`: `|B| ≤ 4` (uniformly in `c, a, b`; the "absolute constant" of the source proof:
  the part over `s ≤ 1` is `≤ 1` since `|sin s/s| ≤ 1`, and the tail over `[1,y]` is `≤ 3` by integration by parts);
* `sine_integral_le_lipschitz`: `|B| ≤ |c| (b − a)`.
No value of `∫₀^∞ sin s/s` is needed (the Cauchy-type multiplier differences suffice).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Set Filter Topology

namespace QuantumNLS.SineIntegral

/-- `sin s / s`. -/
def sg (s : ℝ) : ℝ := Real.sin s / s

theorem abs_sg_le_one {s : ℝ} (hs : 0 < s) : |sg s| ≤ 1 := by
  unfold sg
  rw [abs_div, abs_of_pos hs, div_le_one hs]
  have := Real.abs_sin_le_abs (x := s)
  rwa [abs_of_pos hs] at this

theorem continuousOn_sg {x y : ℝ} (hx : 0 < x) : ContinuousOn sg (Set.Icc x y) :=
  ContinuousOn.div Real.continuous_sin.continuousOn continuousOn_id
    (fun s hs => (lt_of_lt_of_le hx hs.1).ne')

theorem intInt_sg {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : IntervalIntegrable sg volume x y := by
  have := continuousOn_sg (y := y) hx
  rw [← uIcc_of_le hxy] at this
  exact this.intervalIntegrable

/-- Integral of `sg` over a short interval: `|∫_x^y sg| ≤ y − x`. -/
theorem sg_integral_le_length {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    |∫ s in x..y, sg s| ≤ y - x := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := y) (C := 1)
    (f := sg) (fun s hs => by
      rw [uIoc_of_le hxy] at hs
      rw [Real.norm_eq_abs]
      exact abs_sg_le_one (lt_of_lt_of_le hx hs.1.le))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hxy)] at h
  simpa using h

/-- Tail bound by integration by parts. -/
theorem sg_tail_bound {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) : |∫ s in x..y, sg s| ≤ 3 := by
  have hpos : ∀ s ∈ Set.Icc x y, 0 < s := fun s hs => lt_of_lt_of_le one_pos (hx.trans hs.1)
  have hG : ∀ s ∈ Set.uIcc x y,
      HasDerivAt (fun s => -Real.cos s / s) (sg s + Real.cos s / s ^ 2) s := by
    intro s hs
    rw [uIcc_of_le hxy] at hs
    have hs0 : s ≠ 0 := (hpos s hs).ne'
    have h1 : HasDerivAt (fun s => -Real.cos s) (Real.sin s) s :=
      ((Real.hasDerivAt_cos s).neg).congr_deriv (by simp)
    have h2 := h1.div (hasDerivAt_id s) hs0
    have h3 : HasDerivAt (fun s => -Real.cos s / s) ((Real.sin s * s - (-Real.cos s) * 1) / s ^ 2) s := h2
    convert h3 using 1
    unfold sg
    field_simp
    ring
  have hcont : ContinuousOn (fun s => sg s + Real.cos s / s ^ 2) (Set.uIcc x y) := by
    rw [uIcc_of_le hxy]
    refine (continuousOn_sg (y := y) (by linarith)).add ?_
    exact ContinuousOn.div Real.continuous_cos.continuousOn (by fun_prop)
      (fun s hs => (pow_pos (lt_of_lt_of_le one_pos (hx.trans hs.1)) 2).ne')
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hG hcont.intervalIntegrable
  -- ∫ cos/s² is bounded by 1/x - 1/y
  have hH : ∀ s ∈ Set.uIcc x y, HasDerivAt (fun s => -s⁻¹) (s ^ 2)⁻¹ s := by
    intro s hs
    rw [uIcc_of_le hxy] at hs
    have hs0 : s ≠ 0 := (hpos s hs).ne'
    exact ((hasDerivAt_inv hs0).neg).congr_deriv (by simp)
  have hHint : ∫ s in x..y, (s ^ 2)⁻¹ = -y⁻¹ - -x⁻¹ := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt hH ?_
    have : ContinuousOn (fun s : ℝ => (s ^ 2)⁻¹) (Set.uIcc x y) := by
      rw [uIcc_of_le hxy]
      exact ContinuousOn.inv₀ (by fun_prop) (fun s hs => (pow_pos (hpos s hs) 2).ne')
    exact this.intervalIntegrable
  have hcos : ContinuousOn (fun s : ℝ => Real.cos s / s ^ 2) (Set.uIcc x y) := by
    rw [uIcc_of_le hxy]
    exact ContinuousOn.div Real.continuous_cos.continuousOn (by fun_prop)
      (fun s hs => (pow_pos (hpos s hs) 2).ne')
  have hsg : IntervalIntegrable sg volume x y := intInt_sg (by linarith) hxy
  have hsplit : ∫ s in x..y, (sg s + Real.cos s / s ^ 2) =
      (∫ s in x..y, sg s) + ∫ s in x..y, Real.cos s / s ^ 2 :=
    intervalIntegral.integral_add hsg hcos.intervalIntegrable
  have hinv : IntervalIntegrable (fun s : ℝ => (s ^ 2)⁻¹) volume x y := by
    have : ContinuousOn (fun s : ℝ => (s ^ 2)⁻¹) (Set.uIcc x y) := by
      rw [uIcc_of_le hxy]
      exact ContinuousOn.inv₀ (by fun_prop) (fun s hs => (pow_pos (hpos s hs) 2).ne')
    exact this.intervalIntegrable
  have hbd : |∫ s in x..y, Real.cos s / s ^ 2| ≤ x⁻¹ - y⁻¹ := by
    calc |∫ s in x..y, Real.cos s / s ^ 2| ≤ ∫ s in x..y, |Real.cos s / s ^ 2| :=
          intervalIntegral.abs_integral_le_integral_abs hxy
      _ ≤ ∫ s in x..y, (s ^ 2)⁻¹ :=
          intervalIntegral.integral_mono_on hxy hcos.intervalIntegrable.abs hinv (fun s hs => by
            have hs2 : 0 < s ^ 2 := pow_pos (hpos s hs) 2
            rw [abs_div, abs_of_pos hs2]
            calc |Real.cos s| / s ^ 2 ≤ 1 / s ^ 2 :=
                  div_le_div_of_nonneg_right (Real.abs_cos_le_one s) hs2.le
              _ = (s ^ 2)⁻¹ := one_div _)
      _ = x⁻¹ - y⁻¹ := by rw [hHint]; ring
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := hx.trans hxy
  have e1 : |-Real.cos y / y| ≤ 1 := by
    rw [abs_div, abs_neg, abs_of_pos hy0, div_le_one hy0]
    exact (Real.abs_cos_le_one y).trans hy1
  have e2 : |-Real.cos x / x| ≤ 1 := by
    rw [abs_div, abs_neg, abs_of_pos hx0, div_le_one hx0]
    exact (Real.abs_cos_le_one x).trans hx
  have e3 : x⁻¹ - y⁻¹ ≤ 1 := by
    have : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
    have : 0 ≤ y⁻¹ := inv_nonneg.2 hy0.le
    linarith
  have hA : ∫ s in x..y, sg s = (-Real.cos y / y - -Real.cos x / x) - ∫ s in x..y, Real.cos s / s ^ 2 := by
    have := hFTC
    rw [hsplit] at this
    linarith
  rw [hA]
  rw [abs_le] at e1 e2 hbd ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, hbd.1, hbd.2]

/-- Uniform bound `|∫_x^y sin s/s| ≤ 4` for `0 < x ≤ y`. -/
theorem sg_integral_le_four {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : |∫ s in x..y, sg s| ≤ 4 := by
  rcases le_or_gt 1 x with h1 | h1
  · linarith [sg_tail_bound h1 hxy]
  · rcases le_or_gt y 1 with h2 | h2
    · have := sg_integral_le_length hx hxy
      linarith
    · have hs1 := sg_integral_le_length hx h1.le
      have hs2 := sg_tail_bound le_rfl h2.le
      rw [← intervalIntegral.integral_add_adjacent_intervals (intInt_sg hx h1.le)
        (intInt_sg one_pos h2.le)]
      calc |(∫ s in x..1, sg s) + ∫ s in (1:ℝ)..y, sg s| ≤
          |∫ s in x..1, sg s| + |∫ s in (1:ℝ)..y, sg s| := abs_add_le _ _
        _ ≤ 4 := by linarith

/-- `sin(ct)/t = c · sg(ct)` for `t > 0`, `c ≠ 0`. -/
theorem sin_div_eq {c t : ℝ} (hc : c ≠ 0) (ht : 0 < t) : Real.sin (c * t) / t = c * sg (c * t) := by
  unfold sg
  have : c * t ≠ 0 := mul_ne_zero hc ht.ne'
  field_simp

theorem sine_integral_pos {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, Real.sin (c * t) / t = ∫ s in c * a..c * b, sg s := by
  have h1 : ∫ t in a..b, Real.sin (c * t) / t = ∫ t in a..b, c * sg (c * t) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hab] at ht
    exact sin_div_eq hc.ne' (lt_of_lt_of_le ha ht.1)
  rw [h1, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left sg hc.ne',
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- **Uniform bound** `|∫_a^b sin(ct)/t dt| ≤ 4`. -/
theorem sine_integral_le_four (c : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |∫ t in a..b, Real.sin (c * t) / t| ≤ 4 := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have h : ∫ t in a..b, Real.sin (c * t) / t = -∫ t in a..b, Real.sin ((-c) * t) / t := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      simp only [neg_mul, Real.sin_neg, neg_div, neg_neg]
    rw [h, abs_neg, sine_integral_pos (neg_pos.2 hc) ha hab]
    exact sg_integral_le_four (mul_pos (neg_pos.2 hc) ha) (mul_le_mul_of_nonneg_left hab (neg_pos.2 hc).le)
  · subst hc; simp
  · rw [sine_integral_pos hc ha hab]
    exact sg_integral_le_four (mul_pos hc ha) (mul_le_mul_of_nonneg_left hab hc.le)

/-- **Lipschitz bound** `|∫_a^b sin(ct)/t dt| ≤ |c| (b − a)`. -/
theorem sine_integral_le_lipschitz (c : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |∫ t in a..b, Real.sin (c * t) / t| ≤ |c| * (b - a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := |c|)
    (f := fun t => Real.sin (c * t) / t) (fun t ht => by
      rw [uIoc_of_le hab] at ht
      have ht0 : 0 < t := lt_of_lt_of_le ha ht.1.le
      rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
      calc |Real.sin (c * t)| ≤ |c * t| := Real.abs_sin_le_abs
        _ = |c| * t := by rw [abs_mul, abs_of_pos ht0])
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at h
  exact h

#print axioms sine_integral_le_four
#print axioms sine_integral_le_lipschitz

end QuantumNLS.SineIntegral
