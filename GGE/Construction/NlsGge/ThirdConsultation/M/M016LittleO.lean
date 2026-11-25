import Mathlib

                                                                                             
                                                                                              
                                                                                                        
                                                                                                                    
                                                                                        
                                                                                                                    
                                                                                              
                                                                                                               
                                                                                                                    
                                                                                                              
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace NlsGge.ThirdConsultation.M016CL
noncomputable section

/-- Disc bound from a little-o bound along one sequence. -/
theorem disc_bound_of_littleO (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0) (a : ℕ → ℂ) (m : ℕ)
    (w : ℕ → ℂ) (hw0 : ∀ j, w j ≠ 0) (hwt : Tendsto w atTop (𝓝 0))
    (ho : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      ‖g (w j) - ∑ k ∈ Finset.range (m + 1), a k * w j ^ k‖ ≤ ε * ‖w j‖ ^ m) :
    ∃ C' r : ℝ, 0 ≤ C' ∧ 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      ‖g z - ∑ k ∈ Finset.range (m + 1), a k * z ^ k‖ ≤ C' * ‖z‖ ^ (m + 1) := by
  set h : ℂ → ℂ := fun z => g z - ∑ k ∈ Finset.range (m + 1), a k * z ^ k with hh
  have hpoly : AnalyticAt ℂ (fun z : ℂ => ∑ k ∈ Finset.range (m + 1), a k * z ^ k) 0 := by
    have : (fun z : ℂ => ∑ k ∈ Finset.range (m + 1), a k * z ^ k) =
        fun z => ∑ k ∈ Finset.range (m + 1), (fun k z => a k * z ^ k) k z := rfl
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
    obtain ⟨n, k, hk, hk0, hkeq⟩ := (hA.exists_eventuallyEq_pow_smul_nonzero_iff).2 hnot
    have hkc : ContinuousAt k 0 := hk.continuousAt
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
    by_cases hmn : m + 1 ≤ n
    · refine ⟨2 * ‖k 0‖, min (min r1 r2) 1, by positivity, by positivity, fun z hz => ?_⟩
      have hz1 : ‖z‖ < r1 := lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_left _ _))
      have hz2 : ‖z‖ < r2 := lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_right _ _))
      have hz3 : ‖z‖ < 1 := lt_of_lt_of_le hz (min_le_right _ _)
      have he := hball (show dist z 0 < r2 by simpa [dist_eq_norm] using hz2)
      simp only [hh, sub_zero, smul_eq_mul] at he
      rw [he, norm_mul, norm_pow]
      have hpow : ‖z‖ ^ n ≤ ‖z‖ ^ (m + 1) := pow_le_pow_of_le_one (norm_nonneg _) hz3.le hmn
      have hkb := (hk1 z hz1).1
      calc ‖z‖ ^ n * ‖k z‖ ≤ ‖z‖ ^ (m + 1) * (2 * ‖k 0‖) :=
            mul_le_mul hpow hkb (norm_nonneg _) (by positivity)
        _ = (2 * ‖k 0‖) * ‖z‖ ^ (m + 1) := by ring
    · exfalso
      push_neg at hmn
      have hnm : n ≤ m := by omega
      have hk0n : 0 < ‖k 0‖ := norm_pos_iff.2 hk0
      have hε : 0 < ‖k 0‖ / 4 := by linarith
      have hmin : (0 : ℝ) < min (min r1 r2) 1 := by positivity
      have hev : ∀ᶠ j in atTop, ‖w j‖ < min (min r1 r2) 1 :=
        hwt.norm.eventually (gt_mem_nhds (by simpa using hmin))
      obtain ⟨j, hj1, hj2⟩ := (hev.and (ho (‖k 0‖ / 4) hε)).exists
      have hwn : 0 < ‖w j‖ := norm_pos_iff.2 (hw0 j)
      have hj1' : ‖w j‖ < r1 := lt_of_lt_of_le hj1 ((min_le_left _ _).trans (min_le_left _ _))
      have hj2' : ‖w j‖ < r2 := lt_of_lt_of_le hj1 ((min_le_left _ _).trans (min_le_right _ _))
      have hj3' : ‖w j‖ < 1 := lt_of_lt_of_le hj1 (min_le_right _ _)
      have he := hball (show dist (w j) 0 < r2 by simpa [dist_eq_norm] using hj2')
      simp only [hh, sub_zero, smul_eq_mul] at he
      rw [he, norm_mul, norm_pow] at hj2
      have hlow := (hk1 (w j) hj1').2
      have hpow : ‖w j‖ ^ m ≤ ‖w j‖ ^ n := pow_le_pow_of_le_one (norm_nonneg _) hj3'.le hnm
      have hwpn : 0 < ‖w j‖ ^ n := pow_pos hwn n
      have h1 : ‖w j‖ ^ n * (‖k 0‖ / 2) ≤ ‖w j‖ ^ n * ‖k (w j)‖ :=
        mul_le_mul_of_nonneg_left hlow hwpn.le
      have h2 : ‖k 0‖ / 4 * ‖w j‖ ^ m ≤ ‖k 0‖ / 4 * ‖w j‖ ^ n :=
        mul_le_mul_of_nonneg_left hpow hε.le
      nlinarith [mul_pos hwpn hk0n]

/-- A polynomial of degree ≤ m which is O(|z|^(m+1)) on a disc has all coefficients zero. -/
theorem poly_coeff_eq_zero (b : ℕ → ℂ) (m : ℕ) (C r : ℝ) (hr : 0 < r)
    (hb : ∀ z : ℂ, ‖z‖ < r → ‖∑ i ∈ Finset.range (m + 1), b i * z ^ i‖ ≤ C * ‖z‖ ^ (m + 1)) :
    ∀ k ≤ m, b k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  set B : ℝ := ∑ i ∈ Finset.range (m + 1), ‖b i‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have key : ∀ t : ℝ, 0 < t → t < min r 1 → ‖b k‖ ≤ (|C| + B) * t := by
    intro t ht htr
    have htr1 : t < r := lt_of_lt_of_le htr (min_le_left _ _)
    have ht1 : t < 1 := lt_of_lt_of_le htr (min_le_right _ _)
    have hnt : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg ht.le]
    have hmem : k ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    have hsplit := Finset.add_sum_erase (Finset.range (m + 1)) (fun i => b i * (t : ℂ) ^ i) hmem
    have hrest : ‖∑ i ∈ (Finset.range (m + 1)).erase k, b i * (t : ℂ) ^ i‖ ≤ B * t ^ (k + 1) := by
      calc ‖∑ i ∈ (Finset.range (m + 1)).erase k, b i * (t : ℂ) ^ i‖
          ≤ ∑ i ∈ (Finset.range (m + 1)).erase k, ‖b i * (t : ℂ) ^ i‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ (Finset.range (m + 1)).erase k, ‖b i‖ * t ^ (k + 1) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [norm_mul, norm_pow, hnt]
            rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with hlt | hgt
            · rw [ih i hlt (by omega), norm_zero, zero_mul, zero_mul]
            · exact mul_le_mul_of_nonneg_left
                (pow_le_pow_of_le_one ht.le ht1.le (by omega)) (norm_nonneg _)
        _ ≤ ∑ i ∈ Finset.range (m + 1), ‖b i‖ * t ^ (k + 1) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun _ _ _ => by positivity)
        _ = B * t ^ (k + 1) := by rw [hB, Finset.sum_mul]
    have hS := hb (t : ℂ) (by rw [hnt]; exact htr1)
    rw [← hsplit, hnt] at hS
    have htri : ‖b k * (t : ℂ) ^ k‖ ≤
        ‖b k * (t : ℂ) ^ k + ∑ i ∈ (Finset.range (m + 1)).erase k, b i * (t : ℂ) ^ i‖ +
          ‖∑ i ∈ (Finset.range (m + 1)).erase k, b i * (t : ℂ) ^ i‖ := by
      have e : b k * (t : ℂ) ^ k =
          (b k * (t : ℂ) ^ k + ∑ i ∈ (Finset.range (m + 1)).erase k, b i * (t : ℂ) ^ i) -
            ∑ i ∈ (Finset.range (m + 1)).erase k, b i * (t : ℂ) ^ i := by ring
      calc ‖b k * (t : ℂ) ^ k‖ = ‖(b k * (t : ℂ) ^ k +
            ∑ i ∈ (Finset.range (m + 1)).erase k, b i * (t : ℂ) ^ i) -
            ∑ i ∈ (Finset.range (m + 1)).erase k, b i * (t : ℂ) ^ i‖ := by rw [← e]
        _ ≤ _ := norm_sub_le _ _
    rw [norm_mul, norm_pow, hnt] at htri
    have hC : C * t ^ (m + 1) ≤ |C| * t ^ (k + 1) := by
      have hp : t ^ (m + 1) ≤ t ^ (k + 1) := pow_le_pow_of_le_one ht.le ht1.le (by omega)
      have hp0 : 0 ≤ t ^ (m + 1) := by positivity
      calc C * t ^ (m + 1) ≤ |C| * t ^ (m + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) hp0
        _ ≤ |C| * t ^ (k + 1) := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
    have htk : 0 < t ^ k := pow_pos ht k
    have hfin : ‖b k‖ * t ^ k ≤ ((|C| + B) * t) * t ^ k := by
      have e2 : ((|C| + B) * t) * t ^ k = |C| * t ^ (k + 1) + B * t ^ (k + 1) := by ring
      rw [e2]
      linarith
    exact le_of_mul_le_mul_right hfin htk
  by_contra hne
  have hpos : 0 < ‖b k‖ := norm_pos_iff.2 hne
  set D : ℝ := |C| + B + 1 with hD
  have hD0 : 0 < D := by have := abs_nonneg C; linarith
  set t : ℝ := min (min r 1 / 2) (‖b k‖ / (2 * D)) with ht
  have ht0 : 0 < t := by
    have : 0 < min r 1 := lt_min hr one_pos
    positivity
  have htr : t < min r 1 := by
    have : 0 < min r 1 := lt_min hr one_pos
    calc t ≤ min r 1 / 2 := min_le_left _ _
      _ < min r 1 := by linarith
  have hkey := key t ht0 htr
  have htD : D * t ≤ ‖b k‖ / 2 := by
    have : t ≤ ‖b k‖ / (2 * D) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have : (|C| + B) * t ≤ D * t := by
    apply mul_le_mul_of_nonneg_right _ ht0.le
    linarith
  linarith

/-- Little-o coefficient comparison: disc bound and identification of the Taylor coefficients. -/
theorem coeff_match_littleO (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0) (a : ℕ → ℂ) (m : ℕ)
    (w : ℕ → ℂ) (hw0 : ∀ j, w j ≠ 0) (hwt : Tendsto w atTop (𝓝 0))
    (ho : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      ‖g (w j) - ∑ k ∈ Finset.range (m + 1), a k * w j ^ k‖ ≤ ε * ‖w j‖ ^ m) :
    (∃ C' r : ℝ, 0 ≤ C' ∧ 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      ‖g z - ∑ k ∈ Finset.range (m + 1), a k * z ^ k‖ ≤ C' * ‖z‖ ^ (m + 1)) ∧
    (∀ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesAt g p 0 →
      ∀ k ≤ m, a k = p.coeff k) := by
  obtain ⟨C', r, hC', hr, hdisc⟩ := disc_bound_of_littleO g hg a m w hw0 hwt ho
  refine ⟨⟨C', r, hC', hr, hdisc⟩, fun p hp => ?_⟩
  obtain ⟨c, hc⟩ := (hp.isBigO_sub_partialSum_pow (m + 1)).bound
  obtain ⟨r2, hr2, hball⟩ := Metric.eventually_nhds_iff.1 hc
  have hb : ∀ z : ℂ, ‖z‖ < min r r2 →
      ‖∑ i ∈ Finset.range (m + 1), (a i - p.coeff i) * z ^ i‖ ≤ (C' + |c|) * ‖z‖ ^ (m + 1) := by
    intro z hz
    have h1 := hdisc z (lt_of_lt_of_le hz (min_le_left _ _))
    have h2 := hball (show dist z 0 < r2 by
      simpa [dist_eq_norm] using lt_of_lt_of_le hz (min_le_right _ _))
    simp only [zero_add, norm_pow, norm_norm] at h2
    have hps : p.partialSum (m + 1) z = ∑ i ∈ Finset.range (m + 1), p.coeff i * z ^ i := by
      unfold FormalMultilinearSeries.partialSum
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
    rw [hps] at h2
    have e : ∑ i ∈ Finset.range (m + 1), (a i - p.coeff i) * z ^ i =
        (g z - ∑ i ∈ Finset.range (m + 1), p.coeff i * z ^ i) -
          (g z - ∑ i ∈ Finset.range (m + 1), a i * z ^ i) := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [e]
    have hz0 : 0 ≤ ‖z‖ ^ (m + 1) := by positivity
    calc _ ≤ ‖g z - ∑ i ∈ Finset.range (m + 1), p.coeff i * z ^ i‖ +
          ‖g z - ∑ i ∈ Finset.range (m + 1), a i * z ^ i‖ := norm_sub_le _ _
      _ ≤ c * ‖z‖ ^ (m + 1) + C' * ‖z‖ ^ (m + 1) := add_le_add h2 h1
      _ ≤ (C' + |c|) * ‖z‖ ^ (m + 1) := by nlinarith [le_abs_self c]
  intro k hk
  have := poly_coeff_eq_zero (fun i => a i - p.coeff i) m (C' + |c|) (min r r2) (lt_min hr hr2) hb k hk
  exact sub_eq_zero.1 this

end
end NlsGge.ThirdConsultation.M016CL
