import Mathlib
import NlsGge.GK38.AbelianOriginalFiniteCircleExcision
import NlsGge.GK38.AbelianFiniteHoleOuterGeometry
import NlsGge.GK38.StdRootBranchesProducts
import NlsGge.GK38.StdRootBranchesConvergence
import NlsGge.GK38.PairRealBridge

/- M017 CXGK PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M017CxGK.lean. GK38 only. Spectral inputs for the complex M-017 contour route:
   * quot_analyticAt: z^k Δ'(z)/s(z) is analytic at every cut-free point (φ ∈ gkW).
   * partial_sum_circle: for all large ν, the circle |z| = νπ + π/2 is cut-free and the symmetric sum of the actual
     abelian periods of z^k Δ' over |n| ≤ ν equals the circle integral of z^k Δ'/s (landed
     `p6Original_finite_circle_period_excision38`, reindexed from `range (2ν+1)` to `Icc (−ν) ν`). -/

set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M017Cx

theorem quot_analyticAt (φ : PotPair) (hφ : φ ∈ gkW) (k : ℕ) (z : ℂ) (hz : z ∉ gapSegments38 φ) :
    AnalyticAt ℂ (fun w : ℂ => w ^ k * deriv (discrim φ) w / canonRoot38 φ w) z := by
  have hD : AnalyticAt ℂ (deriv (discrim φ)) z := ((analyticOnNhd_discrim_z φ) z (mem_univ z)).deriv
  have hs : AnalyticAt ℂ (canonRoot38 φ) z :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2) (f := fun w : ℂ => (φ, w))
      (canonRoot_analytic38 (φ, z) ⟨hφ, hz⟩) ((analyticAt_const (v := φ)).prod analyticAt_id)
  exact ((analyticAt_id.pow k).mul hD).div hs (canonRoot_ne_zero38 φ hφ z hz)

theorem sum_range_shift (ν : ℕ) (g : ℤ → ℂ) :
    ∑ m ∈ Finset.range (2 * ν + 1), g ((m : ℤ) - ν) = ∑ n ∈ Finset.Icc (-(ν : ℤ)) ν, g n := by
  refine Finset.sum_nbij' (fun m : ℕ => (m : ℤ) - ν) (fun n : ℤ => (n + ν).toNat) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Icc]
    omega
  · intro b hb
    rw [Finset.mem_Icc] at hb
    rw [Finset.mem_range]
    omega
  · intro a _
    omega
  · intro b hb
    rw [Finset.mem_Icc] at hb
    omega
  · intro a _
    rfl

theorem partial_sum_circle (φ : PotPair) (hφ : φ ∈ gkW) (k : ℕ) :
    ∃ L : ℕ, ∀ ν : ℕ, L ≤ ν →
      (∀ z ∈ sphere (0 : ℂ) (ν * Real.pi + Real.pi / 2), z ∉ gapSegments38 φ) ∧
      ∑ n ∈ Finset.Icc (-(ν : ℤ)) ν, abelianPeriod38 n φ (fun z : ℂ => z ^ k * deriv (discrim φ) z) =
        ∮ z in C(0, ν * Real.pi + Real.pi / 2), z ^ k * deriv (discrim φ) z / canonRoot38 φ z := by
  have hfam := isolating_family38 φ hφ
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => z ^ k * deriv (discrim φ) z) univ :=
    (analyticOnNhd_id.pow k).mul (analyticOnNhd_discrim_z φ).deriv
  obtain ⟨L1, h1⟩ := p6Original_finite_circle_period_excision38 φ hφ (discC φ) (discR φ) hfam _ hf
  obtain ⟨L2, h2⟩ := p6Actual_midpoint_square_annulus_cut_domain38 φ (discC φ) (discR φ) hfam
  refine ⟨max L1 L2, fun ν hν => ⟨?_, ?_⟩⟩
  · intro z hz
    have hzn : ‖z‖ = ν * Real.pi + Real.pi / 2 := by simpa using hz
    exact h2 ν (le_trans (le_max_right _ _) hν) z hzn.ge
      (hzn ▸ Complex.abs_re_le_norm z)
  · rw [← sum_range_shift ν, ← (h1 ν (le_trans (le_max_left _ _) hν)).2]

end NlsGge.ThirdConsultation.M017Cx
