import NlsGge.GK38.StdRootBranchesPairBounds

/-! Actual D4 summability precedes the common coordinate and paired bounds. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem root_common_coordinates38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ gkW ∧ ∃ D G : ℝ,
      0 ≤ D ∧ 0 ≤ G ∧ ∀ φ ∈ V, ∀ n : ℤ,
        ‖tauN φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ D ∧ ‖gamma2 φ n‖ ≤ G := by
  obtain ⟨V, hV, hVW, B, hB, h⟩ := tauGamma_common_value_bound38 discC discR
    isolating_selectors_admissible38 φ₀ hφ₀
  refine ⟨V, hV, hVW, Real.sqrt B, B, Real.sqrt_nonneg B, hB, fun φ hφ n => ?_⟩
  have hφdata := h φ hφ
  have hmean := hφdata.1.sum_le_tsum ({n} : Finset ℤ) (fun _ _ => sq_nonneg _)
  have hmean' : ‖tauN φ n - (n : ℂ) * (Real.pi : ℂ)‖^2 ≤ B := by
    have hpoint : ‖tauN φ n - (n : ℂ) * (Real.pi : ℂ)‖^2 ≤
        ∑' k : ℤ, ‖tauN φ k - (k : ℂ) * (Real.pi : ℂ)‖^2 := by
      simpa only [Finset.sum_singleton, tauN] using hmean
    exact hpoint.trans hφdata.2.2.2.1
  have hgamma := hφdata.2.2.1.sum_le_tsum ({n} : Finset ℤ) (fun _ _ => norm_nonneg _)
  have hgamma' : ‖gamma2 φ n‖ ≤ B := by
    have hpoint : ‖gamma2 φ n‖ ≤ ∑' k : ℤ, ‖gamma2 φ k‖ := by
      simpa only [Finset.sum_singleton, gamma2] using hgamma
    exact hpoint.trans hφdata.2.2.2.2.2
  refine ⟨?_, hgamma'⟩
  nlinarith [Real.sq_sqrt hB, Real.sqrt_nonneg B, norm_nonneg (tauN φ n - (n : ℂ) * (Real.pi : ℂ))]

theorem root_pair_local_bound38 (p : PotPair × ℂ) (hp : p ∈ rootDomain38) :
    ∃ r : ℝ, 0 < r ∧ ∃ R' : ℝ, ∀ q ∈ ball p r, q ∈ rootDomain38 → ∀ m : ℕ,
      ‖Lib.pairDev (fun n => rootFactor38 n q) m‖ ≤ Lib.pairMaj (rootTauQ38 q) R' m := by
  obtain ⟨V, hV, _hVW, D, G, hD, hG, hcoord⟩ := root_common_coordinates38 p.1 hp.1
  let R : ℝ := ‖p.2‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpot : ∀ᶠ q : PotPair × ℂ in 𝓝 p, q.1 ∈ V :=
    continuous_fst.continuousAt.preimage_mem_nhds hV
  have hz : ∀ᶠ q : PotPair × ℂ in 𝓝 p, ‖q.2‖ < R :=
    continuous_snd.norm.continuousAt.eventually_lt_const (by dsimp [R]; linarith)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hpot.and hz)
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * (D + R) / Real.pi)
  have hsep : 2 * (D + R) ≤ (M : ℝ) * Real.pi :=
    le_of_lt ((div_lt_iff₀ Real.pi_pos).mp hM)
  refine ⟨r, hr, rootPairRadius38 R (rootPairS38 D G R M), fun q hq hqU m => ?_⟩
  have hqdata := hsub hq
  exact root_pair_common_bound38 q hqU hD hG hR M hsep
    (fun n => (hcoord q.1 hqdata.1 n).1) (fun n => (hcoord q.1 hqdata.1 n).2)
    hqdata.2.le m

end
end NlsGge.GK38
