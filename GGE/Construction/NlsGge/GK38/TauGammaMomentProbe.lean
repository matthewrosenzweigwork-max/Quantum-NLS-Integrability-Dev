import NlsGge.GK38.TauGammaContourGlue
import NlsGge.GK38.IsolatingRealProbe
import NlsGge.GK38.RealTypeSpectrumConstant

/-! Actual distinct contours about a repeated negative root and an open nonfree central pair. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

def tauGamma_probe_radius38 (n : ℤ) : ℝ := if n = -1 then Real.pi / 8 else Real.pi / 4

theorem tauGamma_probe_alternate_family38 :
    IsolatingFamily38 (0 : PotPair) countingCenter38 tauGamma_probe_radius38 := by
  have hR : ∀ n : ℤ, 0 < tauGamma_probe_radius38 n := by
    intro n
    unfold tauGamma_probe_radius38
    split_ifs <;> positivity
  have hRle : ∀ n : ℤ, tauGamma_probe_radius38 n ≤ Real.pi / 4 := by
    intro n
    unfold tauGamma_probe_radius38
    split_ifs <;> nlinarith [Real.pi_pos]
  obtain ⟨c, hg⟩ := tail_comparable_geometry38 countingCenter38 tauGamma_probe_radius38 1
    (fun n => ⟨hR n, by simp [countingCenter38]⟩)
    (by
      intro m n hmn
      change (countingCenter38 m).re < (countingCenter38 n).re
      rw [countingCenter_re38, countingCenter_re38]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hmn) Real.pi_pos)
    (by
      intro m n hmn
      have ht := countingCenter_separated38 hmn
      rw [dist_eq_norm]
      nlinarith [hRle m, hRle n, Real.pi_pos])
    (by
      intro n hn
      refine ⟨rfl, ?_⟩
      have hne : n ≠ -1 := by intro he; subst n; norm_num at hn
      simp [tauGamma_probe_radius38, hne])
  have hs := real_spectral_of_gap_circles38 0 countingCenter38 tauGamma_probe_radius38 c 1 hg
    (by
      intro n x hx
      rw [(isolating_free_gap_endpoints38 n).1, (isolating_free_gap_endpoints38 n).2] at hx
      have he : x = (n : ℝ) * Real.pi := le_antisymm hx.2 hx.1
      change (x : ℂ) ∈ ball (countingCenter38 n) (tauGamma_probe_radius38 n)
      rw [he]
      have hc : (((n : ℝ) * Real.pi : ℝ) : ℂ) = countingCenter38 n := by simp [countingCenter38]
      rw [hc]
      exact mem_ball_self (hR n))
  exact ⟨c, 1, hg, by simpa only [realSlice_zero] using hs⟩

theorem tauGamma_probe_distinct_contours38 (k : ℕ) :
    (Real.pi / 8 : ℝ) ≠ Real.pi / 4 ∧
    CircleIntegrable (momentIntegrand38 0 k) (-(Real.pi : ℂ)) (Real.pi / 4) ∧
    CircleIntegrable (momentIntegrand38 0 k) (-(Real.pi : ℂ)) (Real.pi / 8) ∧
    circleIntegral (momentIntegrand38 0 k) (-(Real.pi : ℂ)) (Real.pi / 4) =
      circleIntegral (momentIntegrand38 0 k) (-(Real.pi : ℂ)) (Real.pi / 8) := by
  refine ⟨by nlinarith [Real.pi_pos], ?_⟩
  have h := moment_contour_independent38 0 countingCenter38 countingCenter38
    (fun _ => Real.pi / 4) tauGamma_probe_radius38 isolating_free_family_probe38
    tauGamma_probe_alternate_family38 (-1) k
  simpa [countingCenter38, tauGamma_probe_radius38] using h

theorem tauGamma_probe_free_negative_moments38 :
    fixedMoment38 0 countingCenter38 tauGamma_probe_radius38 (-1) 0 = 2 ∧
    fixedMoment38 0 countingCenter38 tauGamma_probe_radius38 (-1) 1 = -2 * (Real.pi : ℂ) ∧
    fixedMoment38 0 countingCenter38 tauGamma_probe_radius38 (-1) 2 = 2 * (Real.pi : ℂ) ^ 2 := by
  simp only [fixedMoment_pair38 _ _ _ tauGamma_probe_alternate_family38, lamMinus_zero38,
    lamPlus_zero38, countingCenter38]
  constructor
  · norm_num
  · constructor <;> norm_num <;> ring

theorem tauGamma_probe_nonfree_open_mean38 :
    tauN (realSlice (constL2 1)) 0 = 0 ∧ q2 (realSlice (constL2 1)) 0 = 2 ∧
      gamma2 (realSlice (constL2 1)) 0 = 4 := by
  have hw := realSlice_mem_gkW (constL2 1)
  have h := selected_pair_identities38 discC discR isolating_selectors_admissible38 _ hw 0
  have hl := realType_const_central_labels38
  simp only [hl.1, hl.2] at h
  dsimp only [tauN, q2, gamma2]
  norm_num at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end
end NlsGge.GK38
