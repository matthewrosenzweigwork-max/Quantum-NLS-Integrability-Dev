import NlsGge.GK38.AbelianLargeCircleSeparation
import NlsGge.GK38.PeriodicAsymptotics
import NlsGge.GK38.AbelianPeriods

/-! Actual large circles avoid EVERY spectral cut. Genuine contour integrability
is earned from the actual analytic quotient before any contour-limit identity. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

theorem p6LargeCircle_eventual_avoid_segments38 (a b : ℤ → ℂ)
    (ha : Summable (fun m : ℤ => ‖a m-(m : ℂ)*(Real.pi : ℂ)‖^2))
    (hb : Summable (fun m : ℤ => ‖b m-(m : ℂ)*(Real.pi : ℂ)‖^2)) :
    ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν → ∀ z : ℂ,
      ‖z‖=ν*Real.pi+Real.pi/2 → ∀ m : ℤ, z ∉ segment ℝ (a m) (b m) := by
  obtain ⟨Na,hNa⟩ := Lib.circle_sum_bound ha (half_pos Real.pi_pos)
  obtain ⟨Nb,hNb⟩ := Lib.circle_sum_bound hb (half_pos Real.pi_pos)
  refine ⟨max Na Nb,fun ν hν z hz m hzm => ?_⟩
  let c : ℂ := (m : ℂ)*(Real.pi : ℂ)
  let r : ℝ := (Real.pi/2)*Lib.circDist ν m
  have hadiv := hNa ν ((le_max_left _ _).trans hν) ({m} : Finset ℤ)
  have hbdiv := hNb ν ((le_max_right _ _).trans hν) ({m} : Finset ℤ)
  simp only [Finset.sum_singleton] at hadiv hbdiv
  have hanorm : ‖a m-c‖ ≤ r := (div_le_iff₀ (Lib.circDist_pos ν m)).mp hadiv
  have hbnorm : ‖b m-c‖ ≤ r := (div_le_iff₀ (Lib.circDist_pos ν m)).mp hbdiv
  have hamem : a m ∈ closedBall c r := by
    simpa only [mem_closedBall,dist_eq_norm] using hanorm
  have hbmem : b m ∈ closedBall c r := by
    simpa only [mem_closedBall,dist_eq_norm] using hbnorm
  have hsegment : segment ℝ (a m) (b m) ⊆ closedBall c r :=
    (convex_closedBall c r).segment_subset hamem hbmem
  have hsmall : ‖z-c‖ ≤ r := by
    simpa only [mem_closedBall,dist_eq_norm] using hsegment hzm
  have hlarge : Real.pi*Lib.circDist ν m ≤ ‖z-c‖ :=
    (Lib.pi_mul_dd_le hz m).trans_eq (norm_sub_rev c z)
  have hpos : 0 < Real.pi*Lib.circDist ν m :=
    mul_pos Real.pi_pos (Lib.circDist_pos ν m)
  dsimp only [r] at hsmall
  nlinarith

theorem p6Actual_large_circle_cut_complement38 (φ : PotPair) :
    ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν → ∀ z : ℂ,
      ‖z‖=ν*Real.pi+Real.pi/2 → z ∉ gapSegments38 φ := by
  obtain ⟨N,hN⟩ := p6LargeCircle_eventual_avoid_segments38 (lamMinus φ) (lamPlus φ)
    (periodic_minus_summable38 φ) (periodic_plus_summable38 φ)
  refine ⟨N,fun ν hν z hz hcut => ?_⟩
  obtain ⟨m,hm⟩ := mem_iUnion.mp hcut
  exact hN ν hν z hz m hm

theorem p6Actual_large_circle_full_quotient_integrable38 (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) :
    ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν → ∀ n : ℤ,
      CircleIntegrable (fun z : ℂ => p2FullNumerator38 n s z/canonRoot38 φ z)
        0 (ν*Real.pi+Real.pi/2) := by
  obtain ⟨N,hN⟩ := p6Actual_large_circle_cut_complement38 φ
  refine ⟨N,fun ν hν n => ?_⟩
  have hsub : sphere (0 : ℂ) (ν*Real.pi+Real.pi/2) ⊆ actionCutDomain38 φ := by
    intro z hz
    exact hN ν hν z (by simpa only [dist_zero_right] using mem_sphere.mp hz)
  exact ((p2Quotient_analytic38 φ hφ (p2FullNumerator38 n s)
    (p2FullNumerator_entire38 n s)).continuousOn.mono hsub).circleIntegrable (by positivity)

end
end NlsGge.GK38
