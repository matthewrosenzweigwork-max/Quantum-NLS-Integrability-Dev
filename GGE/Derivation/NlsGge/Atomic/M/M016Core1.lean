import Mathlib

/- M016 CORE1 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/M/M016Core1.lean,
   namespace NlsGge.ThirdConsultation.M016C. SUPPORT (no packet increment), Mathlib only.
   The coefficient-identification step of Pro's M-016 route ("obtain convergence of the whole Laurent series from M052's
   analytic inverted chart and identify each coefficient from WKB on the real axis"): if g is analytic at 0 and agrees with
   a polynomial Σ_{k<K} a_k w^k up to C|w|^K along ONE sequence w_j → 0 (w_j ≠ 0), then the same polynomial approximates g
   to order K on a whole punctured disc: ∃ C' r > 0, ∀ |z| < r, |g z − Σ_{k<K} a_k z^k| ≤ C'|z|^K. (Isolated zeros:
   h = g − poly is eventually 0 or (z^m)·k with k(0) ≠ 0; m < K contradicts the sequence bound.) -/
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace NlsGge.ThirdConsultation.M016C
noncomputable section

theorem coeff_match (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0) (a : ℕ → ℂ) (K : ℕ)
    (w : ℕ → ℂ) (hw0 : ∀ j, w j ≠ 0) (hwt : Tendsto w atTop (𝓝 0)) (C : ℝ)
    (hb : ∀ j, ‖g (w j) - ∑ k ∈ Finset.range K, a k * w j ^ k‖ ≤ C * ‖w j‖ ^ K) :
    ∃ C' r : ℝ, 0 ≤ C' ∧ 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      ‖g z - ∑ k ∈ Finset.range K, a k * z ^ k‖ ≤ C' * ‖z‖ ^ K := by
  set h : ℂ → ℂ := fun z => g z - ∑ k ∈ Finset.range K, a k * z ^ k with hh
  have hpoly : AnalyticAt ℂ (fun z : ℂ => ∑ k ∈ Finset.range K, a k * z ^ k) 0 := by
    have : (fun z : ℂ => ∑ k ∈ Finset.range K, a k * z ^ k) =
        fun z => ∑ k ∈ Finset.range K, (fun k z => a k * z ^ k) k z := rfl
    rw [this]
    exact Finset.analyticAt_fun_sum _ (fun k _ => analyticAt_const.mul (analyticAt_id.pow k))
  have hA : AnalyticAt ℂ h 0 := hg.sub hpoly
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with hz | hnz
  · obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hz
    refine ⟨0, r, le_rfl, hr, fun z hzr => ?_⟩
    have := hball (by simpa [dist_eq_norm] using hzr)
    simp only [hh] at this
    rw [this, norm_zero, zero_mul]
  · have hnot : ¬∀ᶠ z in 𝓝 (0 : ℂ), h z = 0 := by
      intro h0
      have h0' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), h z = 0 := h0.filter_mono nhdsWithin_le_nhds
      obtain ⟨z, hz1, hz2⟩ := (h0'.and hnz).exists
      exact hz2 hz1
    obtain ⟨m, k, hk, hk0, hkeq⟩ := (hA.exists_eventuallyEq_pow_smul_nonzero_iff).2 hnot
    have hkc : ContinuousAt k 0 := hk.continuousAt
    -- bound near 0 for k
    obtain ⟨r1, hr1, hk1⟩ : ∃ r1 > 0, ∀ z : ℂ, ‖z‖ < r1 →
        ‖k z‖ ≤ 2 * ‖k 0‖ ∧ ‖k 0‖ / 2 ≤ ‖k z‖ := by
      have hpos : 0 < ‖k 0‖ / 2 := by have := norm_pos_iff.2 hk0; linarith
      obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 hkc (‖k 0‖ / 2) hpos
      refine ⟨δ, hδ, fun z hz => ?_⟩
      have h1 : ‖k z - k 0‖ < ‖k 0‖ / 2 := by
        have := hδb (show dist z 0 < δ by simpa [dist_eq_norm] using hz)
        simpa [dist_eq_norm] using this
      have h2 := norm_sub_norm_le (k z) (k 0)
      have h3 := norm_sub_norm_le (k 0) (k z)
      rw [norm_sub_rev] at h3
      constructor <;> linarith
    obtain ⟨r2, hr2, hball⟩ := Metric.eventually_nhds_iff.1 hkeq
    by_cases hmK : K ≤ m
    · refine ⟨2 * ‖k 0‖, min (min r1 r2) 1, by positivity, by positivity, fun z hz => ?_⟩
      have hz1 : ‖z‖ < r1 := lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_left _ _))
      have hz2 : ‖z‖ < r2 := lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_right _ _))
      have hz3 : ‖z‖ < 1 := lt_of_lt_of_le hz (min_le_right _ _)
      have he := hball (show dist z 0 < r2 by simpa [dist_eq_norm] using hz2)
      simp only [hh, sub_zero, smul_eq_mul] at he
      rw [he, norm_mul, norm_pow]
      have hpow : ‖z‖ ^ m ≤ ‖z‖ ^ K := pow_le_pow_of_le_one (norm_nonneg _) hz3.le hmK
      have hkb := (hk1 z hz1).1
      calc ‖z‖ ^ m * ‖k z‖ ≤ ‖z‖ ^ K * (2 * ‖k 0‖) :=
            mul_le_mul hpow hkb (norm_nonneg _) (by positivity)
        _ = (2 * ‖k 0‖) * ‖z‖ ^ K := by ring
    · exfalso
      push_neg at hmK
      -- along the sequence: ‖k 0‖/2 ‖w‖^m ≤ C ‖w‖^K, contradiction as w → 0
      have hev : ∀ᶠ j in atTop, ‖w j‖ < min r1 r2 :=
        (hwt.norm.eventually (gt_mem_nhds (by simpa using lt_min hr1 hr2)))
      have hk0p : 0 < ‖k 0‖ / 2 := by have := norm_pos_iff.2 hk0; linarith
      have hsmall : Tendsto (fun j => C * ‖w j‖ ^ (K - m)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun j => ‖w j‖ ^ (K - m)) atTop (𝓝 0) := by
          have := (hwt.norm).pow (K - m)
          simpa [zero_pow (by omega : K - m ≠ 0)] using this
        simpa using h1.const_mul C
      obtain ⟨j, hj1, hj2⟩ := (hev.and (hsmall.eventually (gt_mem_nhds hk0p))).exists
      have hwj := hw0 j
      have hwn : 0 < ‖w j‖ := norm_pos_iff.2 hwj
      have hj1' : ‖w j‖ < r1 := lt_of_lt_of_le hj1 (min_le_left _ _)
      have hj2' : ‖w j‖ < r2 := lt_of_lt_of_le hj1 (min_le_right _ _)
      have he := hball (show dist (w j) 0 < r2 by simpa [dist_eq_norm] using hj2')
      simp only [hh, sub_zero, smul_eq_mul] at he
      have hbj := hb j
      rw [he, norm_mul, norm_pow] at hbj
      have hlow := (hk1 (w j) hj1').2
      have h1 : ‖w j‖ ^ m * (‖k 0‖ / 2) ≤ C * ‖w j‖ ^ K :=
        (mul_le_mul_of_nonneg_left hlow (by positivity)).trans hbj
      have hsplit : ‖w j‖ ^ K = ‖w j‖ ^ m * ‖w j‖ ^ (K - m) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit] at h1
      have hm0 : 0 < ‖w j‖ ^ m := pow_pos hwn m
      have h2 : ‖k 0‖ / 2 ≤ C * ‖w j‖ ^ (K - m) := by
        have : ‖w j‖ ^ m * (‖k 0‖ / 2) ≤ ‖w j‖ ^ m * (C * ‖w j‖ ^ (K - m)) := by linarith [h1]
        exact le_of_mul_le_mul_left this hm0
      linarith

end
end NlsGge.ThirdConsultation.M016C
