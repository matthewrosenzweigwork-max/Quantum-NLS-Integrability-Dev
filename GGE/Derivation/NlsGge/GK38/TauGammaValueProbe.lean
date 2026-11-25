import NlsGge.GK38.TauGammaCriticalMoments
import NlsGge.GK38.TauGammaValueBounds
import NlsGge.GK38.TauGammaRealAnchors
import NlsGge.GK38.TauGammaMomentProbe

/-! The critical singleton, actual common square sums, and a nonfree negative collapsed gap. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem tauGamma_probe_critical_negative_integral38 :
    CircleIntegrable (fun z => z * deriv (deriv (discrim 0)) z / deriv (discrim 0) z)
      (-(Real.pi : ℂ)) (Real.pi / 8) ∧
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      circleIntegral (fun z => z * deriv (deriv (discrim 0)) z / deriv (discrim 0) z)
        (-(Real.pi : ℂ)) (Real.pi / 8) = -(Real.pi : ℂ) := by
  have hi := critical_moment_circleIntegrable38 0 countingCenter38 tauGamma_probe_radius38
    tauGamma_probe_alternate_family38 (-1)
  have hm := critical_fixedMoment38 0 countingCenter38 tauGamma_probe_radius38
    tauGamma_probe_alternate_family38 (-1)
  simpa [tauGamma_probe_radius38, lamDot_zero38, countingCenter38] using And.intro hi hm

theorem tauGamma_probe_nonfree_negative_values38 :
    tauN (realSlice (constL2 1)) (-1) = ((-Real.sqrt (Real.pi ^ 2 + 1) : ℝ) : ℂ) ∧
      gamma2 (realSlice (constL2 1)) (-1) = 0 := by
  have hw := realSlice_mem_gkW (constL2 1)
  have hl := realType_const_negative_labels38
  have ht := tau_pair_mean38 discC discR isolating_selectors_admissible38 _ hw (-1)
  have hg := gamma2_pair_gap38 discC discR isolating_selectors_admissible38 _ hw (-1)
  dsimp only [tauN, gamma2]
  rw [ht, hg, hl.1, hl.2]
  constructor
  · ring
  · simp

theorem tauGamma_probe_actual_common_square_sums38 :
    ∃ V : Set PotPair, V ∈ 𝓝 (realSlice (constL2 1)) ∧ V ⊆ gkW ∧ ∃ B : ℝ,
      0 ≤ B ∧ ∀ φ ∈ V,
        Summable (fun n : ℤ => ‖tauN φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
        Summable (fun n : ℤ => ‖lamPlus φ n - lamMinus φ n‖ ^ 2) ∧
        Summable (fun n : ℤ => ‖gamma2 φ n‖) ∧
        (∑' n : ℤ, ‖tauN φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ B ∧
        (∑' n : ℤ, ‖lamPlus φ n - lamMinus φ n‖ ^ 2) ≤ B ∧
        (∑' n : ℤ, ‖gamma2 φ n‖) ≤ B :=
  tauGamma_common_value_bound38 discC discR isolating_selectors_admissible38 _
    (realSlice_mem_gkW (constL2 1))

end
end NlsGge.GK38
