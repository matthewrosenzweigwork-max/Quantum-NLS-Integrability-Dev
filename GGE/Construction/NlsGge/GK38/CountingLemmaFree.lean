import NlsGge.GK38.CountingLemmaGeometry
import NlsGge.GK38.Lib.RoucheProbe

/-! # S1: exact free multiplicities and quarter-radius counts -/

set_option autoImplicit false

open Filter Topology Set Metric

namespace NlsGge.GK38

noncomputable section

/-- Every bounded disc has finite characteristic-divisor support; no totalized default is used. -/
theorem counting_zeroMult_support_finite38 (φ : PotPair) (c : ℂ) (r : ℝ) :
    (Function.support (Lib.zeroMult (perChar φ) (ball c r))).Finite :=
  Lib.zeroMult_support_finite
    ((analyticOnNhd_perChar_z φ).mono (subset_univ _)).meromorphicOn
    (isCompact_closedBall c r) ball_subset_closedBall

theorem counting_free_zero_iff38 (z : ℂ) : perChar 0 z = 0 ↔ Complex.sin z = 0 := by
  rw [perChar_zero]
  simp

theorem counting_free_order38 (z : ℂ) :
    analyticOrderNatAt (perChar 0) z = if Complex.sin z = 0 then 2 else 0 := by
  have he : perChar 0 = (fun _ : ℂ => (-4 : ℂ)) * Complex.sin ^ 2 := by
    funext w
    exact perChar_zero w
  have hc : analyticOrderAt (fun _ : ℂ => (-4 : ℂ)) z = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (by norm_num)
  have hord : analyticOrderAt (perChar 0) z = analyticOrderAt (Complex.sin ^ 2) z := by
    rw [he, analyticOrderAt_mul analyticAt_const (Complex.analyticAt_sin.pow 2), hc, zero_add]
  have hnat := congrArg ENat.toNat hord
  change analyticOrderNatAt (perChar 0) z = analyticOrderNatAt (Complex.sin ^ 2) z at hnat
  rw [analyticOrderNatAt_pow Complex.analyticAt_sin, Lib.order_sin] at hnat
  simpa using hnat

/-- The finite free lattice set is unchanged at the exact radius Nπ+π/4. -/
theorem counting_mem_sinZeros38 {N : ℕ} {z : ℂ} :
    z ∈ Lib.sinZeros N ↔ Complex.sin z = 0 ∧ ‖z‖ < countingRadius38 N := by
  classical
  constructor
  · intro hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hlow : |n| ≤ (N : ℤ) := abs_le.mpr ⟨hn1, hn2⟩
    have hnorm := countingCenter_low_norm38 hlow
    refine ⟨Complex.sin_eq_zero_iff.mpr ⟨n, rfl⟩, ?_⟩
    change ‖countingCenter38 n‖ < countingRadius38 N
    unfold countingRadius38
    linarith [Real.pi_pos]
  · rintro ⟨hz, hnorm⟩
    obtain ⟨n, rfl⟩ := Complex.sin_eq_zero_iff.mp hz
    change ‖countingCenter38 n‖ < countingRadius38 N at hnorm
    have hlow : |n| ≤ (N : ℤ) := by
      by_contra h
      have hfar := countingCenter_far_norm38 (lt_of_not_ge h)
      unfold countingRadius38 at hnorm
      linarith [Real.pi_pos]
    exact Finset.mem_image.mpr ⟨n, Finset.mem_Icc.mpr (abs_le.mp hlow), rfl⟩

theorem counting_free_central_multiset38 (N : ℕ) :
    Lib.zeroMultiset (perChar 0) (ball (0 : ℂ) (countingRadius38 N)) =
      (Lib.sinZeros N).val + (Lib.sinZeros N).val := by
  classical
  have hfin := counting_zeroMult_support_finite38 0 0 (countingRadius38 N)
  refine Multiset.ext' fun z => ?_
  rw [Lib.count_zeroMultiset_ball
    ((analyticOnNhd_perChar_z 0).mono (subset_univ _)), counting_free_order38,
    Multiset.count_add]
  by_cases hz : z ∈ Lib.sinZeros N
  · have hm := counting_mem_sinZeros38.mp hz
    rw [Multiset.count_eq_one_of_mem (Lib.sinZeros N).nodup hz]
    have hb : z ∈ ball (0 : ℂ) (countingRadius38 N) := by
      simpa only [mem_ball, dist_zero_right] using hm.2
    rw [ite_eq_left hb, ite_eq_left hm.1]
  · rw [Multiset.count_eq_zero_of_notMem (by simpa using hz)]
    by_cases hb : z ∈ ball (0 : ℂ) (countingRadius38 N)
    · have hsin : Complex.sin z ≠ 0 := by
        intro h
        exact hz (counting_mem_sinZeros38.mpr
          ⟨h, by simpa only [mem_ball, dist_zero_right] using hb⟩)
      simp only [ite_eq_left hb, ite_eq_right hsin]
    · simp only [ite_eq_right hb]

theorem counting_free_central_card38 (N : ℕ) :
    Multiset.card (Lib.zeroMultiset (perChar 0)
      (ball (0 : ℂ) (countingRadius38 N))) = 4 * N + 2 := by
  rw [counting_free_central_multiset38, Multiset.card_add]
  change (Lib.sinZeros N).card + (Lib.sinZeros N).card = _
  rw [Lib.card_sinZeros]
  omega

theorem counting_free_small_multiset38 (n : ℤ) :
    Lib.zeroMultiset (perChar 0) (ball (countingCenter38 n) (Real.pi / 4)) =
      Multiset.replicate 2 (countingCenter38 n) := by
  have hfin := counting_zeroMult_support_finite38 0 (countingCenter38 n) (Real.pi / 4)
  have he := Lib.zeroMultiset_ball_eq_replicate (by positivity : 0 < Real.pi / 4)
    ((analyticOnNhd_perChar_z 0).mono (subset_univ _)) (a := countingCenter38 n)
    (fun z hz hzn => ?_)
  · have hsin : Complex.sin (countingCenter38 n) = 0 :=
      Complex.sin_eq_zero_iff.mpr ⟨n, rfl⟩
    simpa only [counting_free_order38, ite_eq_left hsin] using he
  · intro hz0
    obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp ((counting_free_zero_iff38 z).mp hz0)
    have hmn : m ≠ n := by
      intro h
      apply hzn
      simpa only [h, countingCenter38] using hm
    have hsep := countingCenter_separated38 hmn
    have hclose : ‖countingCenter38 m - countingCenter38 n‖ ≤ Real.pi / 4 := by
      simpa only [mem_closedBall, dist_eq_norm, hm, countingCenter38] using hz
    linarith [Real.pi_pos]

theorem counting_free_small_card38 (n : ℤ) :
    Multiset.card (Lib.zeroMultiset (perChar 0)
      (ball (countingCenter38 n) (Real.pi / 4))) = 2 := by
  rw [counting_free_small_multiset38, Multiset.card_replicate]

end
end NlsGge.GK38
