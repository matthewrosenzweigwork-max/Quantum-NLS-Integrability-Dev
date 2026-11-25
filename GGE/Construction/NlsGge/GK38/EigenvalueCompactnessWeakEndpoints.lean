import NlsGge.GK38.EigenvalueCompactnessCorrectIndex
import NlsGge.GK38.EigenvalueCompactnessWeakClusters
import NlsGge.GK38.EigenvalueCompactnessClusterSaturation
import NlsGge.GK38.EigenvalueCompactnessOrderedClusters

/-! # S7: both actual endpoint labels are weakly sequentially continuous -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem gapEndpoints_weak_localization38 (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hw : IsWeakLim u u₀) (n : ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      |actualGapLowerAllE02_38 (u k) n - actualGapLowerAllE02_38 u₀ n| < ε ∧
        |actualGapUpperAllE02_38 (u k) n - actualGapUpperAllE02_38 u₀ n| < ε := by
  let L := actualGapLowerAllE02_38 u₀ n
  let U := actualGapUpperAllE02_38 u₀ n
  obtain ⟨R, hR, hindexL⟩ := endpoint_weak_correct_index38 u u₀ hw n L (Or.inl rfl)
  by_cases hc : L = U
  · obtain ⟨r, hr, hrsmall, hcount⟩ := endpoint_weak_cluster38 u u₀ hw n L (Or.inl rfl)
      (min ε R) (lt_min hε hR)
    have hre : r < ε := hrsmall.trans_le (min_le_left _ _)
    have hrr : r < R := hrsmall.trans_le (min_le_right _ _)
    filter_upwards [hindexL, hcount] with k hk hi
    have hp := endpoint_cluster_card_two_pair38 (u k) n (L : ℂ) r
      (fun z hz hzero => hk z (ball_subset_ball hrr.le hz) hzero)
      (by simpa only [L, U, hc, ite_true] using hi)
    have hl : |actualGapLowerAllE02_38 (u k) n - L| < r := by
      simpa only [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hp.1
    have hu : |actualGapUpperAllE02_38 (u k) n - L| < r := by
      simpa only [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hp.2
    refine ⟨hl.trans hre, ?_⟩
    change |actualGapUpperAllE02_38 (u k) n - U| < ε
    rw [← hc]
    exact hu.trans hre
  · have hLU : L < U := lt_of_le_of_ne (gap_endpoint_levels38 u₀ n).1 hc
    obtain ⟨S, hS, hindexU⟩ := endpoint_weak_correct_index38 u u₀ hw n U (Or.inr rfl)
    let δ := min ε ((U-L)/3)
    have hδ : 0 < δ := lt_min hε (by linarith)
    obtain ⟨r, hr, hrsmall, hcountL⟩ := endpoint_weak_cluster38 u u₀ hw n L (Or.inl rfl)
      (min δ R) (lt_min hδ hR)
    obtain ⟨s, hs, hssmall, hcountU⟩ := endpoint_weak_cluster38 u u₀ hw n U (Or.inr rfl)
      (min δ S) (lt_min hδ hS)
    have hrδ : r < δ := hrsmall.trans_le (min_le_left _ _)
    have hsδ : s < δ := hssmall.trans_le (min_le_left _ _)
    have hrR : r < R := hrsmall.trans_le (min_le_right _ _)
    have hsS : s < S := hssmall.trans_le (min_le_right _ _)
    have hδε : δ ≤ ε := min_le_left _ _
    have hδgap : δ ≤ (U-L)/3 := min_le_right _ _
    have hsep : r+s < U-L := by linarith
    filter_upwards [hindexL, hindexU, hcountL, hcountU] with k hkL hkU hkcardL hkcardU
    have hcardL : 0 < Multiset.card (Lib.zeroMultiset (perChar (realSlice (u k))) (ball (L : ℂ) r)) := by
      rw [hkcardL]
      split_ifs <;> norm_num
    have hcardU : 0 < Multiset.card (Lib.zeroMultiset (perChar (realSlice (u k))) (ball (U : ℂ) s)) := by
      rw [hkcardU]
      split_ifs <;> norm_num
    have hL := endpoint_cluster_has_pair38 (u k) n L r
      (fun z hz hzero => hkL z (ball_subset_ball hrR.le hz) hzero) hcardL
    have hU := endpoint_cluster_has_pair38 (u k) n U s
      (fun z hz hzero => hkU z (ball_subset_ball hsS.le hz) hzero) hcardU
    have hp := endpoint_two_ordered_clusters38 (u k) n L U r s hsep hL hU
    exact ⟨hp.1.trans (hrδ.trans_le hδε), hp.2.trans (hsδ.trans_le hδε)⟩

theorem gapEndpoints_weak_tendsto38 (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hw : IsWeakLim u u₀) (n : ℤ) :
    Tendsto (fun k => actualGapLowerAllE02_38 (u k) n) atTop (𝓝 (actualGapLowerAllE02_38 u₀ n)) ∧
      Tendsto (fun k => actualGapUpperAllE02_38 (u k) n) atTop (𝓝 (actualGapUpperAllE02_38 u₀ n)) := by
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [gapEndpoints_weak_localization38 u u₀ hw n ε hε] with k hk
    exact (Real.dist_eq _ _).symm ▸ hk.1
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [gapEndpoints_weak_localization38 u u₀ hw n ε hε] with k hk
    exact (Real.dist_eq _ _).symm ▸ hk.2

end
end NlsGge.GK38
