import NlsGge.GK38.EigenvalueCompactnessDefs
import NlsGge.GK38.RealTypeMultiplicity
import NlsGge.GK38.Lib.Rouche

/-! # S7: exact reference endpoint circles and multiplicities

The accepted S6 orders are ascribed to the reviewed open/closed formulation.
-/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem endpoint_order38 (u : PhysicalL2) (n : ℤ) (x : ℝ) (hx : EndpointAt38 u n x) :
    analyticOrderAt (perChar (realSlice u)) (x : ℂ) =
      if actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n then 2 else 1 := by
  have he : analyticOrderAt (perChar (realSlice u)) (x : ℂ) =
      if actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n then (1 : ℕ∞) else 2 := by
    rcases hx with rfl | rfl
    · exact order_at_gapEnd u n
    · exact order_at_gapUpper38 u n
  by_cases hc : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n
  · simpa only [hc, lt_self_iff_false, ite_false, ite_true] using he
  · have hs := lt_of_le_of_ne (gap_endpoint_levels38 u n).1 hc
    simpa only [hc, hs, ite_false, ite_true] using he

theorem endpoint_root38 (u : PhysicalL2) (n : ℤ) (x : ℝ) (hx : EndpointAt38 u n x) :
    perChar (realSlice u) (x : ℂ) = 0 := by
  rcases hx with rfl | rfl
  · exact (gap_endpoint_roots38 u n).1
  · exact (gap_endpoint_roots38 u n).2

theorem endpoint_reference_cluster38 (u : PhysicalL2) (n : ℤ) (x : ℝ)
    (hx : EndpointAt38 u n x) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧
      (∀ z ∈ closedBall (x : ℂ) r, z ≠ (x : ℂ) → perChar (realSlice u) z ≠ 0) ∧
      Multiset.card (Lib.zeroMultiset (perChar (realSlice u)) (ball (x : ℂ) r)) =
        if actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n then 2 else 1 := by
  have ha := analyticOnNhd_perChar_z (realSlice u) (x : ℂ) (mem_univ _)
  have hnt : analyticOrderAt (perChar (realSlice u)) (x : ℂ) ≠ ⊤ := by
    rw [endpoint_order38 u n x hx]; split_ifs <;> norm_num
  have hpunct : ∀ᶠ z in 𝓝[≠] (x : ℂ), perChar (realSlice u) z ≠ 0 := by
    rcases ha.eventually_eq_zero_or_eventually_ne_zero with he | he
    · exact False.elim (hnt (analyticOrderAt_eq_top.mpr he))
    · exact he
  rw [eventually_nhdsWithin_iff] at hpunct
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hpunct
  let r := min ε δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r < ε := by have := min_le_left ε δ; dsimp [r]; linarith
  have hrδ : r < δ := by have := min_le_right ε δ; dsimp [r]; linarith
  have hiso : ∀ z ∈ closedBall (x : ℂ) r, z ≠ (x : ℂ) → perChar (realSlice u) z ≠ 0 := by
    intro z hz hne
    exact hb ((mem_closedBall.mp hz).trans_lt hrδ) (by simpa only [mem_compl_iff, mem_singleton_iff] using hne)
  refine ⟨r, hr, hrε, hiso, ?_⟩
  rw [Lib.zeroMultiset_ball_eq_replicate hr ((analyticOnNhd_perChar_z _).mono (subset_univ _)) hiso,
    Multiset.card_replicate]
  simp only [analyticOrderNatAt, endpoint_order38 u n x hx]
  split_ifs <;> rfl

end
end NlsGge.GK38
