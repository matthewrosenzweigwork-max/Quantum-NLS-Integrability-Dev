import NlsGge.Weights.Entire
set_option autoImplicit false
noncomputable section
namespace NlsGge.Weights

def complexWeightTerm (c : ℕ → ℝ) (z : ℂ) (j : ℕ) : ℂ :=
  (coefficient c j : ℂ) * z ^ (2 * j)

def complexWeightTermDerivative (c : ℕ → ℝ) (z : ℂ) (j : ℕ) : ℂ :=
  (coefficient c j : ℂ) * ((2 * j : ℕ) : ℂ) * z ^ (2 * j - 1)

def complexWeight (c : ℕ → ℝ) (z : ℂ) : ℂ := ∑' j, complexWeightTerm c z j

lemma complexWeightTerm_norm (lower : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (z : ℂ) (j : ℕ) :
    ‖complexWeightTerm c z j‖ = weightTerm c ‖z‖ j := by
  simp only [complexWeightTerm, weightTerm, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (coefficient_pos lower c hlower hbound j)]

lemma complexWeightTerm_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (z : ℂ) : Summable (complexWeightTerm c z) := by
  apply Summable.of_norm
  simpa only [complexWeightTerm_norm lower c hlower hbound z] using
    weightTerm_summable lower upper c hlower hbound hupper ‖z‖

lemma complexWeightTermDerivative_norm_le (lower : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (R : ℝ) (hR : 1 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) (j : ℕ) :
    ‖complexWeightTermDerivative c z j‖ ≤ 2 * (j : ℝ) ^ 4 * weightTerm c R j := by
  have hp := (coefficient_pos lower c hlower hbound j).le
  have hjpow : (j : ℝ) ≤ (j : ℝ) ^ (4 : ℕ) := by
    by_cases hj : j = 0
    · simp [hj]
    · apply le_self_pow₀
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
      · norm_num
  have hzpow : ‖z‖ ^ (2 * j - 1) ≤ R ^ (2 * j) :=
    (pow_le_pow_left₀ (norm_nonneg z) hz _).trans
      (pow_le_pow_right₀ hR (Nat.sub_le (2 * j) 1))
  simp only [complexWeightTermDerivative, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (coefficient_pos lower c hlower hbound j),
    Complex.norm_natCast, Nat.cast_mul, Nat.cast_ofNat, Complex.norm_two, Real.norm_two]
  calc
    coefficient c j * (2 * (j : ℝ)) * ‖z‖ ^ (2 * j - 1) ≤
      coefficient c j * (2 * (j : ℝ)) * R ^ (2 * j) := by gcongr
    _ ≤ coefficient c j * (2 * (j : ℝ) ^ 4) * R ^ (2 * j) := by gcongr
    _ = 2 * (j : ℝ) ^ 4 * weightTerm c R j := by unfold weightTerm; ring

lemma complexWeightDerivative_majorant_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (R : ℝ) :
    Summable (fun j : ℕ => 2 * (j : ℝ) ^ 4 * weightTerm c R j) := by
  simpa only [mul_assoc] using
    (fourthMoment_summable lower upper c hlower hbound hupper R).mul_left 2

lemma complexWeightTermDerivative_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (z : ℂ) :
    Summable (complexWeightTermDerivative c z) := by
  apply Summable.of_norm
  exact (complexWeightDerivative_majorant_summable lower upper c hlower hbound hupper
    (max 1 ‖z‖)).of_nonneg_of_le (fun j => norm_nonneg _)
      (complexWeightTermDerivative_norm_le lower c hlower hbound
        (max 1 ‖z‖) (le_max_left _ _) z (le_max_right _ _))

lemma complexWeightTerm_hasDerivAt (c : ℕ → ℝ) (z : ℂ) (j : ℕ) :
    HasDerivAt (fun w : ℂ => complexWeightTerm c w j) (complexWeightTermDerivative c z j) z := by
  convert (hasDerivAt_pow (2 * j) z).const_mul (coefficient c j : ℂ) using 1
  · rfl
  · unfold complexWeightTermDerivative
    ring


lemma complexWeightSeries_tendstoUniformlyOn (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ => ∑ j ∈ Finset.range N, complexWeightTerm c z j)
      (complexWeight c) Filter.atTop (Metric.closedBall (0 : ℂ) R) := by
  apply tendstoUniformlyOn_tsum_nat (weightTerm_summable lower upper c hlower hbound hupper R)
  intro j z hz
  have hzR : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  rw [complexWeightTerm_norm lower c hlower hbound z, weightTerm, weightTerm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hzR _)
    (coefficient_pos lower c hlower hbound j).le

lemma complexWeightDerivativeSeries_tendstoUniformlyOn (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ => ∑ j ∈ Finset.range N, complexWeightTermDerivative c z j)
      (fun z : ℂ => ∑' j, complexWeightTermDerivative c z j)
      Filter.atTop (Metric.closedBall (0 : ℂ) R) := by
  apply tendstoUniformlyOn_tsum_nat
    (complexWeightDerivative_majorant_summable lower upper c hlower hbound hupper (max 1 R))
  intro j z hz
  have hzR : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  exact complexWeightTermDerivative_norm_le lower c hlower hbound (max 1 R)
    (le_max_left _ _) z (hzR.trans (le_max_right _ _)) j

lemma complexWeightSeries_tendstoUniformlyOn_compact (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ => ∑ j ∈ Finset.range N, complexWeightTerm c z j)
      (complexWeight c) Filter.atTop K := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  apply (complexWeightSeries_tendstoUniformlyOn lower upper c hlower hbound hupper R hR.le).mono
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hKR z hz

lemma complexWeightDerivativeSeries_tendstoUniformlyOn_compact (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ => ∑ j ∈ Finset.range N, complexWeightTermDerivative c z j)
      (fun z : ℂ => ∑' j, complexWeightTermDerivative c z j) Filter.atTop K := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  apply (complexWeightDerivativeSeries_tendstoUniformlyOn lower upper c hlower hbound hupper R hR.le).mono
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hKR z hz

lemma complexWeight_hasDerivAt (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (z : ℂ) :
    HasDerivAt (complexWeight c) (∑' j, complexWeightTermDerivative c z j) z := by
  let R : ℝ := max 1 (‖z‖ + 1)
  have hR : 1 ≤ R := le_max_left _ _
  have hzR : ‖z‖ < R := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  have hz : z ∈ Metric.ball (0 : ℂ) R := by simpa only [Metric.mem_ball, dist_zero_right] using hzR
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_self]
    linarith
  apply hasDerivAt_tsum_of_isPreconnected
    (complexWeightDerivative_majorant_summable lower upper c hlower hbound hupper R)
    Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected
    (fun j w hw => complexWeightTerm_hasDerivAt c w j) _ hzero
    (complexWeightTerm_summable lower upper c hlower hbound hupper 0) hz
  intro j w hw
  have hwR : ‖w‖ ≤ R := (by simpa only [Metric.mem_ball, dist_zero_right] using hw : ‖w‖ < R).le
  exact complexWeightTermDerivative_norm_le lower c hlower hbound R hR w hwR j

lemma complexWeight_analyticAt (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (z : ℂ) : AnalyticAt ℂ (complexWeight c) z := by
  have hd : Differentiable ℂ (complexWeight c) :=
    fun w => (complexWeight_hasDerivAt lower upper c hlower hbound hupper w).differentiableAt
  exact hd.analyticAt z

lemma complexWeight_ofReal (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    complexWeight c (r : ℂ) = (weight c r : ℂ) := by
  have hreal := weightTerm_summable lower upper c hlower hbound hupper r
  have hcomplex := complexWeightTerm_summable lower upper c hlower hbound hupper (r : ℂ)
  unfold complexWeight weight
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro j
  simp [complexWeightTerm, weightTerm]

end NlsGge.Weights
