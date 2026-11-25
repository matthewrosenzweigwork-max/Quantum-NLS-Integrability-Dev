import Mathlib

/- M016 HALFNODECORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M016HalfNodeCore.lean. Mathlib only. Generic part of `exterior_primitive_halfNode_eq`
   (Pro R16 §1.1, proof §3 step 6):
   * halfNode_chart_generic: at a point a with cos a = 0, c·sin a = 1, |c| = 1, if 2 cosh F = D and F = −i a + w with
     w small, then |D/2| < 1/2 and F = −i a + log(W + √(1+W²)), W = i c D / 2. Indeed W = sinh w, √(1+W²) = cosh w
     (principal root, Re cosh w > 0), sinh w + cosh w = e^w and log e^w = w.
   * small_w_exists: one radius r with |sinh w| < 1/2, Re cosh w > 0, |w| < 1 on ‖w‖ < r.
   * exists_norm_of_tendsto_comap_inv: a limit along comap (·⁻¹) (𝓝[≠] 0) (= M051's `infinityFilter`) holds outside
     a disc.
   * halfNode_trig, halfNode_norm_ge: cos((j+½)π) = 0, (−1)^j sin((j+½)π) = 1, ‖(j+½)π‖ ≥ |j| − ½.
   * halfNode_generic: the whole step-6 argument for abstract F, D with 2 cosh F = D outside a disc. -/

set_option autoImplicit false
open Set Filter Topology Metric

namespace NlsGge.ThirdConsultation.M016ChartAux

theorem halfNode_chart_generic (a w F D c : ℂ) (hcos : Complex.cos a = 0)
    (hcs : c * Complex.sin a = 1) (hc : ‖c‖ = 1)
    (hF : F = -Complex.I * a + w) (hD : 2 * Complex.cosh F = D)
    (hs : ‖Complex.sinh w‖ < 1 / 2) (hre : 0 < (Complex.cosh w).re) (hw : ‖w‖ < 1) :
    ‖D / 2‖ < 1 / 2 ∧
      F = -Complex.I * a + Complex.log (Complex.I * c * D / 2 +
        Complex.sqrt (1 + (Complex.I * c * D / 2) ^ 2)) := by
  have hsplit : Complex.cosh F = -(Complex.sin a) * Complex.I * Complex.sinh w := by
    have e1 : -Complex.I * a = (-a) * Complex.I := by ring
    rw [hF, Complex.cosh_add, e1, Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_neg,
      Complex.sin_neg, hcos]
    ring
  have hW : Complex.I * c * D / 2 = Complex.sinh w := by
    rw [← hD, hsplit]
    linear_combination (-(Complex.I ^ 2) * Complex.sinh w) * hcs +
      (-(Complex.sinh w)) * Complex.I_sq
  have hsin1 : ‖Complex.sin a‖ = 1 := by
    have h := congrArg norm hcs
    rw [norm_mul, hc, one_mul, norm_one] at h
    exact h
  refine ⟨?_, ?_⟩
  · have hD2 : D / 2 = Complex.cosh F := by rw [← hD]; ring
    rw [hD2, hsplit, norm_mul, norm_mul, norm_neg, hsin1, Complex.norm_I, one_mul, one_mul]
    exact hs
  · rw [hW]
    have h1 : 1 + Complex.sinh w ^ 2 = Complex.cosh w ^ 2 := by rw [Complex.cosh_sq]; ring
    have him : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    rw [h1, Complex.sqrt, Complex.sq_cpow_two_inv hre, Complex.sinh_add_cosh,
      Complex.log_exp (by linarith [neg_abs_le w.im, Real.pi_gt_three])
        (by linarith [le_abs_self w.im, Real.pi_gt_three])]
    exact hF

theorem small_w_exists : ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w‖ < r →
    ‖Complex.sinh w‖ < 1 / 2 ∧ 0 < (Complex.cosh w).re ∧ ‖w‖ < 1 := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousAt_iff.1
    (Complex.continuous_sinh.continuousAt (x := 0)) (1 / 2) (by norm_num)
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousAt_iff.1
    (Complex.continuous_cosh.continuousAt (x := 0)) 1 (by norm_num)
  refine ⟨min (min δ₁ δ₂) 1, by positivity, fun w hw => ?_⟩
  have hw1 : ‖w‖ < δ₁ := lt_of_lt_of_le hw ((min_le_left _ _).trans (min_le_left _ _))
  have hw2 : ‖w‖ < δ₂ := lt_of_lt_of_le hw ((min_le_left _ _).trans (min_le_right _ _))
  have hw3 : ‖w‖ < 1 := lt_of_lt_of_le hw (min_le_right _ _)
  have e1 := h₁ (by rwa [dist_zero_right])
  have e2 := h₂ (by rwa [dist_zero_right])
  rw [Complex.sinh_zero, dist_zero_right] at e1
  rw [Complex.cosh_zero, dist_eq_norm] at e2
  refine ⟨e1, ?_, hw3⟩
  have hre := Complex.abs_re_le_norm (Complex.cosh w - 1)
  rw [Complex.sub_re, Complex.one_re] at hre
  linarith [neg_abs_le ((Complex.cosh w).re - 1)]

theorem exists_norm_of_tendsto_comap_inv (G : ℂ → ℂ)
    (hG : Tendsto G (Filter.comap (fun z : ℂ => z⁻¹) (𝓝[≠] (0 : ℂ))) (𝓝 0)) (r : ℝ) (hr : 0 < r) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, M < ‖z‖ → ‖G z‖ < r := by
  have h := hG.eventually (Metric.ball_mem_nhds (0 : ℂ) hr)
  obtain ⟨t, ht, hsub⟩ := Filter.mem_comap.1 h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 ht
  refine ⟨1 / ε, by positivity, fun z hz => ?_⟩
  have hεpos : 0 < 1 / ε := by positivity
  have hzpos : 0 < ‖z‖ := lt_trans hεpos hz
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  have hmem : z⁻¹ ∈ ball (0 : ℂ) ε ∩ {0}ᶜ := by
    refine ⟨?_, by simpa using hz0⟩
    rw [mem_ball, dist_zero_right, norm_inv, inv_lt_comm₀ hzpos hε, ← one_div]
    exact hz
  have hz' : z ∈ (fun z : ℂ => z⁻¹) ⁻¹' t := hball hmem
  have := hsub hz'
  simpa [mem_ball, dist_zero_right] using this

theorem halfNode_trig (j : ℤ) :
    Complex.cos (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)) = 0 ∧
      (-1 : ℂ) ^ j * Complex.sin (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)) = 1 := by
  have e : ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) = (((j : ℝ) * Real.pi : ℝ) : ℂ) + (Real.pi : ℂ) / 2 := by
    push_cast; ring
  have hcos : Complex.cos (((j : ℝ) * Real.pi : ℝ) : ℂ) = (-1 : ℂ) ^ j := by
    rw [← Complex.ofReal_cos, Real.cos_int_mul_pi]; push_cast; rfl
  have hsin : Complex.sin (((j : ℝ) * Real.pi : ℝ) : ℂ) = 0 := by
    rw [← Complex.ofReal_sin, Real.sin_int_mul_pi]; simp
  rw [e, Complex.cos_add_pi_div_two, Complex.sin_add_pi_div_two, hsin, hcos, neg_zero]
  refine ⟨rfl, ?_⟩
  rw [← mul_zpow]
  norm_num

theorem halfNode_norm_ge (j : ℤ) (hj : 1 ≤ |(j : ℝ)|) :
    |(j : ℝ)| - 1 / 2 ≤ ‖((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)‖ := by
  have e : ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) = ((((j : ℝ) + 1 / 2) * Real.pi : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos]
  have h1 : |(j : ℝ)| ≤ |(j : ℝ) + 1 / 2| + 1 / 2 := by
    calc |(j : ℝ)| = |((j : ℝ) + 1 / 2) + (-(1 / 2))| := by ring_nf
      _ ≤ |(j : ℝ) + 1 / 2| + |(-(1 / 2) : ℝ)| := abs_add_le _ _
      _ = |(j : ℝ) + 1 / 2| + 1 / 2 := by norm_num
  nlinarith [Real.pi_gt_three, abs_nonneg ((j : ℝ) + 1 / 2)]

/-- **Half-node identity, generic form.** If `2 cosh F = D` outside a disc and `F z + i z → 0` at infinity, then at
every half-node `a_j = (j + ½)π` with `|j|` large: `|D(a_j)/2| < 1/2` and `F(a_j)` equals the arcsinh chart value. -/
theorem halfNode_generic (F D : ℂ → ℂ) (R : ℝ)
    (hcosh : ∀ z : ℂ, R < ‖z‖ → 2 * Complex.cosh (F z) = D z)
    (hzero : Tendsto (fun z : ℂ => F z + Complex.I * z)
      (Filter.comap (fun z : ℂ => z⁻¹) (𝓝[≠] (0 : ℂ))) (𝓝 0)) :
    ∃ J : ℕ, ∀ j : ℤ, J ≤ j.natAbs →
      R < ‖((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)‖ ∧
      ‖D (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)) / 2‖ < 1 / 2 ∧
      F (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)) =
        -Complex.I * (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)) +
          Complex.log (Complex.I * (-1 : ℂ) ^ j * D (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)) / 2 +
            Complex.sqrt (1 + (Complex.I * (-1 : ℂ) ^ j *
              D (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)) / 2) ^ 2)) := by
  obtain ⟨r, hr, hsmall⟩ := small_w_exists
  obtain ⟨M, hM, hMz⟩ := exists_norm_of_tendsto_comap_inv _ hzero r hr
  refine ⟨⌈M + |R|⌉₊ + 1, fun j hj => ?_⟩
  set a : ℂ := ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) with ha
  have hjabs : ((j.natAbs : ℕ) : ℝ) = |(j : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hjR : ((⌈M + |R|⌉₊ + 1 : ℕ) : ℝ) ≤ |(j : ℝ)| := by
    rw [← hjabs]; exact_mod_cast hj
  have hceil : M + |R| ≤ (⌈M + |R|⌉₊ : ℝ) := Nat.le_ceil _
  push_cast at hjR
  have hj1 : 1 ≤ |(j : ℝ)| := by linarith [abs_nonneg R]
  have hnorm := halfNode_norm_ge j hj1
  have haM : M < ‖a‖ := by linarith [abs_nonneg R]
  have haR : R < ‖a‖ := by linarith [le_abs_self R]
  have hwr : ‖F a + Complex.I * a‖ < r := hMz a haM
  obtain ⟨hs, hre, hw1⟩ := hsmall _ hwr
  obtain ⟨hcos, hcs⟩ := halfNode_trig j
  have hc : ‖(-1 : ℂ) ^ j‖ = 1 := by rw [norm_zpow, norm_neg, norm_one, one_zpow]
  have key := halfNode_chart_generic a (F a + Complex.I * a) (F a) (D a) ((-1 : ℂ) ^ j) hcos hcs hc
    (by ring) (hcosh a haR) hs hre hw1
  exact ⟨haR, key⟩

end NlsGge.ThirdConsultation.M016ChartAux
