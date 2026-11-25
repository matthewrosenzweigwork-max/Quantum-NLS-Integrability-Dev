import NlsGge.GK38.CountingLemma
import NlsGge.GK38.PairAsymptoticsDerivative

/-! # S2: free critical multiplicities (GK Lemma 6.5, counting part) -/

set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem analyticOnNhd_discrimDeriv38 (φ : PotPair) :
    AnalyticOnNhd ℂ (deriv (discrim φ)) univ :=
  (analyticOnNhd_discrim_z φ).deriv

theorem critical_zeroMult_support_finite38 (φ : PotPair) (c : ℂ) (r : ℝ) :
    (Function.support (Lib.zeroMult (deriv (discrim φ)) (ball c r))).Finite :=
  Lib.zeroMult_support_finite
    ((analyticOnNhd_discrimDeriv38 φ).mono (subset_univ _)).meromorphicOn
    (isCompact_closedBall c r) ball_subset_closedBall

theorem discrimDeriv_zero38 : deriv (discrim 0) = fun z => -2 * Complex.sin z := by
  funext z
  have he : discrim 0 = fun w => 2 * Complex.cos w := funext discrim_zero
  rw [he]
  convert ((Complex.hasDerivAt_cos z).const_mul 2).deriv using 1 <;> ring

theorem critical_free_zero_iff38 (z : ℂ) :
    deriv (discrim 0) z = 0 ↔ Complex.sin z = 0 := by
  rw [discrimDeriv_zero38]
  simp

theorem critical_free_order38 (z : ℂ) :
    analyticOrderNatAt (deriv (discrim 0)) z = if Complex.sin z = 0 then 1 else 0 := by
  have he : deriv (discrim 0) = (fun _ : ℂ => (-2 : ℂ)) * Complex.sin :=
    discrimDeriv_zero38
  have hc : analyticOrderAt (fun _ : ℂ => (-2 : ℂ)) z = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (by norm_num)
  have hord : analyticOrderAt (deriv (discrim 0)) z = analyticOrderAt Complex.sin z := by
    rw [he, analyticOrderAt_mul analyticAt_const Complex.analyticAt_sin, hc, zero_add]
  have hnat := congrArg ENat.toNat hord
  change analyticOrderNatAt (deriv (discrim 0)) z = analyticOrderNatAt Complex.sin z at hnat
  simpa only [Lib.order_sin] using hnat

theorem critical_free_central_multiset38 (N : ℕ) :
    Lib.zeroMultiset (deriv (discrim 0)) (ball (0 : ℂ) (countingRadius38 N)) =
      (Lib.sinZeros N).val := by
  classical
  have hfin := critical_zeroMult_support_finite38 0 0 (countingRadius38 N)
  refine Multiset.ext' fun z => ?_
  rw [Lib.count_zeroMultiset_ball
    ((analyticOnNhd_discrimDeriv38 0).mono (subset_univ _)), critical_free_order38]
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

theorem critical_free_central_card38 (N : ℕ) :
    Multiset.card (Lib.zeroMultiset (deriv (discrim 0))
      (ball (0 : ℂ) (countingRadius38 N))) = 2 * N + 1 := by
  rw [critical_free_central_multiset38]
  exact Lib.card_sinZeros N

theorem critical_free_small_multiset38 (n : ℤ) :
    Lib.zeroMultiset (deriv (discrim 0)) (ball (countingCenter38 n) (Real.pi / 4)) =
      {countingCenter38 n} := by
  have hfin := critical_zeroMult_support_finite38 0 (countingCenter38 n) (Real.pi / 4)
  have he := Lib.zeroMultiset_ball_eq_replicate (by positivity : 0 < Real.pi / 4)
    ((analyticOnNhd_discrimDeriv38 0).mono (subset_univ _)) (a := countingCenter38 n)
    (fun z hz hzn => ?_)
  · have hsin : Complex.sin (countingCenter38 n) = 0 :=
      Complex.sin_eq_zero_iff.mpr ⟨n, rfl⟩
    simpa only [critical_free_order38, ite_eq_left hsin, Multiset.replicate_one] using he
  · intro hz0
    obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp ((critical_free_zero_iff38 z).mp hz0)
    have hmn : m ≠ n := by
      intro h
      apply hzn
      simpa only [h, countingCenter38] using hm
    have hsep := countingCenter_separated38 hmn
    have hclose : ‖countingCenter38 m - countingCenter38 n‖ ≤ Real.pi / 4 := by
      simpa only [mem_closedBall, dist_eq_norm, hm, countingCenter38] using hz
    linarith [Real.pi_pos]

theorem critical_free_small_card38 (n : ℤ) :
    Multiset.card (Lib.zeroMultiset (deriv (discrim 0))
      (ball (countingCenter38 n) (Real.pi / 4))) = 1 := by
  rw [critical_free_small_multiset38, Multiset.card_singleton]

end
end NlsGge.GK38
