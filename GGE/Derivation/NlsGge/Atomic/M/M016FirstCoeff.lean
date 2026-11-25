import Mathlib

/- M016 FIRSTCOEFF PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M016FirstCoeff.lean. Mathlib only. Pro R16 §4 (L362-375), the N = 0 coefficient argument, generic:
   g(w) = F(1/w) + i/w analytic at 0 with g(0) = 0 (the landed `AnalyticAtInfinity` body), 2 cosh F = D outside a disc,
   and the bilinear-mass limit 2t(e^{−t}D(it) − 1) → H. Then a₁ = g'(0) satisfies H = −2i a₁, and
   ‖F z + i z + H/(2iz)‖ ≤ C/‖z‖² outside a disc.
   * taylor_two: g(w) − g'(0) w = w² q(w) with q bounded near 0 (dslope twice, Complex.differentiableOn_dslope).
   * ray_limit_coeff: the ray limit equals −2i g'(0).
   * first_coeff_generic: the exterior O(|z|⁻²) bound.
   * laurent_regroup: Σ_{k=1}^{K} I_k/x^k with I₁ = −H₁, I_k = H_k rewritten in the PrimitiveLaurentCoefficients form. -/

set_option autoImplicit false
open Set Filter Topology Metric

namespace NlsGge.ThirdConsultation.M016ChartAux

theorem taylor_two (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ < r → ‖g w - deriv g 0 * w‖ ≤ C * ‖w‖ ^ 2 := by
  set U : Set ℂ := {z | AnalyticAt ℂ g z} with hU
  have hUn : U ∈ 𝓝 (0 : ℂ) := hg.eventually_analyticAt
  have hgd : DifferentiableOn ℂ g U := fun z hz => (hz : AnalyticAt ℂ g z).differentiableAt.differentiableWithinAt
  have hs : DifferentiableOn ℂ (dslope g 0) U := (Complex.differentiableOn_dslope hUn).2 hgd
  have hq : DifferentiableOn ℂ (dslope (dslope g 0) 0) U := (Complex.differentiableOn_dslope hUn).2 hs
  have hqc : ContinuousAt (dslope (dslope g 0) 0) 0 := (hq.differentiableAt hUn).continuousAt
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hqc 1 one_pos
  refine ⟨δ, ‖dslope (dslope g 0) 0 0‖ + 1, hδ, by positivity, fun w hw => ?_⟩
  have h1 : w * dslope g 0 w = g w := by
    have := sub_smul_dslope g 0 w
    rw [sub_zero, smul_eq_mul, hg0, sub_zero] at this
    exact this
  have h2 : w * dslope (dslope g 0) 0 w = dslope g 0 w - deriv g 0 := by
    have := sub_smul_dslope (dslope g 0) 0 w
    rw [sub_zero, smul_eq_mul, dslope_same] at this
    exact this
  have hrepr : g w - deriv g 0 * w = w ^ 2 * dslope (dslope g 0) 0 w := by
    rw [← h1]
    linear_combination (-w) * h2
  have hb : ‖dslope (dslope g 0) 0 w‖ ≤ ‖dslope (dslope g 0) 0 0‖ + 1 := by
    have h := hδ' (by rwa [dist_zero_right])
    rw [dist_eq_norm] at h
    linarith [norm_sub_norm_le (dslope (dslope g 0) 0 w) (dslope (dslope g 0) 0 0)]
  rw [hrepr, norm_mul, norm_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right hb (by positivity)

theorem ray_limit_coeff (F D : ℂ → ℂ) (R : ℝ)
    (hinf : AnalyticAt ℂ (fun w : ℂ => if w = 0 then 0 else F w⁻¹ + Complex.I * w⁻¹) 0)
    (hcosh : ∀ z : ℂ, R < ‖z‖ → 2 * Complex.cosh (F z) = D z) :
    Tendsto (fun t : ℝ => ((2 * t : ℝ) : ℂ) * (Complex.exp (-(t : ℂ)) * D (Complex.I * t) - 1)) atTop
      (𝓝 (-2 * Complex.I *
        deriv (fun w : ℂ => if w = 0 then 0 else F w⁻¹ + Complex.I * w⁻¹) 0)) := by
  set g : ℂ → ℂ := fun w => if w = 0 then 0 else F w⁻¹ + Complex.I * w⁻¹ with hgdef
  set a : ℂ := deriv g 0 with ha
  have hg0 : g 0 = 0 := if_pos rfl
  have hd : HasDerivAt (fun w => Complex.exp (g w)) (Complex.exp (g 0) * a) 0 :=
    (hinf.differentiableAt.hasDerivAt).cexp
  rw [hg0, Complex.exp_zero, one_mul] at hd
  have hslope := hasDerivAt_iff_tendsto_slope.1 hd
  -- w(t) = (i t)⁻¹ → 0 within ≠ 0
  set w : ℝ → ℂ := fun t => (Complex.I * t)⁻¹ with hwdef
  have hw0 : ∀ t : ℝ, 0 < t → w t ≠ 0 := fun t ht => by
    simp only [hwdef, ne_eq, inv_eq_zero, mul_eq_zero, Complex.I_ne_zero, Complex.ofReal_eq_zero,
      false_or]
    exact ht.ne'
  have hwnorm : ∀ t : ℝ, 0 < t → ‖w t‖ = t⁻¹ := fun t ht => by
    simp only [hwdef, norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg ht.le]
  have hwt : Tendsto w atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, (eventually_gt_atTop 0).mono fun t ht => hw0 t ht⟩
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_inv_atTop_zero.congr' ((eventually_gt_atTop 0).mono fun t ht => (hwnorm t ht).symm)
  have hT1 : Tendsto (fun t => slope (fun w => Complex.exp (g w)) 0 (w t)) atTop (𝓝 a) :=
    hslope.comp hwt
  have hgc : Tendsto (fun t => g (w t)) atTop (𝓝 0) := by
    have := (hinf.continuousAt.tendsto.comp (tendsto_nhdsWithin_iff.1 hwt).1)
    rw [hg0] at this
    exact this
  have h2t : Tendsto (fun t : ℝ => ((2 * t * Real.exp (-(2 * t)) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop (two_pos : (0 : ℝ) < 2))
    have h' : Tendsto (fun t : ℝ => 2 * t * Real.exp (-(2 * t))) atTop (𝓝 0) :=
      h.congr fun t => by simp [Function.comp]
    have := (Complex.continuous_ofReal.tendsto 0).comp h'
    rw [Complex.ofReal_zero] at this
    exact this
  have hT2 : Tendsto (fun t : ℝ => ((2 * t * Real.exp (-(2 * t)) : ℝ) : ℂ) * Complex.exp (-g (w t)))
      atTop (𝓝 0) := by
    have := h2t.mul ((Complex.continuous_exp.tendsto _).comp (hgc.neg))
    simpa using this
  have hlim : Tendsto (fun t : ℝ => (-2 * Complex.I) * slope (fun w => Complex.exp (g w)) 0 (w t) +
      ((2 * t * Real.exp (-(2 * t)) : ℝ) : ℂ) * Complex.exp (-g (w t))) atTop
      (𝓝 (-2 * Complex.I * a + 0)) := (hT1.const_mul _).add hT2
  rw [add_zero] at hlim
  refine hlim.congr' ((eventually_gt_atTop (max R 0)).mono fun t ht => ?_)
  have ht0 : 0 < t := lt_of_le_of_lt (le_max_right _ _) ht
  have htR : R < ‖Complex.I * (t : ℂ)‖ := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    exact lt_of_le_of_lt (le_max_left _ _) ht
  have hwne := hw0 t ht0
  have hgw : g (w t) = F (Complex.I * t) - t := by
    have e1 : g (w t) = F (w t)⁻¹ + Complex.I * (w t)⁻¹ := if_neg hwne
    have e2 : (w t)⁻¹ = Complex.I * t := inv_inv _
    rw [e1, e2]
    linear_combination (t : ℂ) * Complex.I_sq
  have hF : F (Complex.I * t) = t + g (w t) := by rw [hgw]; ring
  have hD := hcosh _ htR
  have hIt : (Complex.I * (t : ℂ)) ≠ 0 := by
    simp [Complex.I_ne_zero, ht0.ne']
  show _ = ((2 * t : ℝ) : ℂ) * (Complex.exp (-(t : ℂ)) * D (Complex.I * t) - 1)
  rw [slope_def_field, sub_zero, hg0, Complex.exp_zero, ← hD, Complex.two_cosh, hF]
  have hexp1 : Complex.exp (-(t : ℂ)) * Complex.exp ((t : ℂ) + g (w t)) = Complex.exp (g (w t)) := by
    rw [← Complex.exp_add]; ring_nf
  have hexp2 : Complex.exp (-(t : ℂ)) * Complex.exp (-((t : ℂ) + g (w t))) =
      ((Real.exp (-(2 * t)) : ℝ) : ℂ) * Complex.exp (-g (w t)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]; push_cast; ring_nf
  have hsplit : Complex.exp (-(t : ℂ)) * (Complex.exp ((t : ℂ) + g (w t)) +
      Complex.exp (-((t : ℂ) + g (w t)))) =
      Complex.exp (g (w t)) + ((Real.exp (-(2 * t)) : ℝ) : ℂ) * Complex.exp (-g (w t)) := by
    rw [mul_add, hexp1, hexp2]
  rw [hsplit]
  have hwt' : w t = (Complex.I * t)⁻¹ := rfl
  rw [hwt', div_inv_eq_mul]
  push_cast
  linear_combination (-2 * (t : ℂ) * (Complex.exp (g (w t)) - 1)) * Complex.I_sq

theorem first_coeff_generic (F D : ℂ → ℂ) (R : ℝ) (H : ℂ)
    (hinf : AnalyticAt ℂ (fun w : ℂ => if w = 0 then 0 else F w⁻¹ + Complex.I * w⁻¹) 0)
    (hcosh : ∀ z : ℂ, R < ‖z‖ → 2 * Complex.cosh (F z) = D z)
    (hmass : Tendsto (fun t : ℝ => ((2 * t : ℝ) : ℂ) *
      (Complex.exp (-(t : ℂ)) * D (Complex.I * t) - 1)) atTop (𝓝 H)) :
    ∃ C R' : ℝ, 0 ≤ C ∧ 0 < R' ∧ ∀ z : ℂ, R' ≤ ‖z‖ →
      ‖F z + Complex.I * z + H / (2 * Complex.I * z)‖ ≤ C / ‖z‖ ^ 2 := by
  set g : ℂ → ℂ := fun w => if w = 0 then 0 else F w⁻¹ + Complex.I * w⁻¹ with hgdef
  have hg0 : g 0 = 0 := if_pos rfl
  have hH : H = -2 * Complex.I * deriv g 0 :=
    tendsto_nhds_unique hmass (ray_limit_coeff F D R hinf hcosh)
  obtain ⟨r, C, hr, hC, hT⟩ := taylor_two g hinf hg0
  refine ⟨C, 2 / r, hC, by positivity, fun z hz => ?_⟩
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  have hzi : ‖z⁻¹‖ < r := by
    rw [norm_inv, inv_lt_comm₀ hzpos hr]
    have : 1 / r < 2 / r := by
      apply div_lt_div_of_pos_right (by norm_num) hr
    rw [one_div] at this
    linarith
  have hgz : g z⁻¹ = F z + Complex.I * z := by
    simp only [hgdef, if_neg (inv_ne_zero hz0), inv_inv]
  have key : F z + Complex.I * z + H / (2 * Complex.I * z) = g z⁻¹ - deriv g 0 * z⁻¹ := by
    rw [hgz, hH]
    field_simp
    ring
  rw [key]
  have := hT z⁻¹ hzi
  rw [norm_inv, inv_pow] at this
  rwa [div_eq_mul_inv]

/-- Finite-sum regrouping: with `I₁ = −H₁` and `I_k = H_k` (k ≥ 2), the WKB Laurent polynomial
`Σ_{k=1}^{K} I_k / x^k` is the `PrimitiveLaurentCoefficients` form (H₁ split off, `dite` over `Icc 2 K`). -/
theorem laurent_regroup (N K : ℕ) (hK1 : 1 ≤ K) (hK : K ≤ N + 1) (Ic : ℕ → ℂ)
    (Hc : (k : ℕ) → 1 ≤ k ∧ k ≤ N + 1 → ℂ) (x y : ℂ)
    (h1 : Ic 1 = -Hc 1 ⟨le_rfl, Nat.succ_le_succ (Nat.zero_le N)⟩)
    (hk : ∀ (k : ℕ) (hk : 1 ≤ k ∧ k ≤ N + 1), 2 ≤ k → Ic k = Hc k hk) :
    y - ∑ k ∈ Finset.Icc 1 K, Ic k / x ^ k =
      y + Hc 1 ⟨le_rfl, Nat.succ_le_succ (Nat.zero_le N)⟩ / x -
        ∑ k ∈ Finset.Icc 2 K, (if hk : 1 ≤ k ∧ k ≤ N + 1 then Hc k hk / x ^ k else 0) := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hK1, Finset.sum_insert (by simp), h1, pow_one]
  have hs : ∑ k ∈ Finset.Icc (1 + 1) K, Ic k / x ^ k =
      ∑ k ∈ Finset.Icc 2 K, (if hk : 1 ≤ k ∧ k ≤ N + 1 then Hc k hk / x ^ k else 0) := by
    refine Finset.sum_congr rfl fun k hkm => ?_
    rw [Finset.mem_Icc] at hkm
    have hkc : 1 ≤ k ∧ k ≤ N + 1 := ⟨by omega, by omega⟩
    rw [dif_pos hkc, hk k hkc (by omega)]
  rw [hs]
  ring

end NlsGge.ThirdConsultation.M016ChartAux
