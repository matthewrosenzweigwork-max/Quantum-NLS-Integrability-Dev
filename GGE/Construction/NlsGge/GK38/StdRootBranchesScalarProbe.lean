import NlsGge.GK38.StdRootBranchesSlit
import NlsGge.GK38.TauGammaMomentProbe
import NlsGge.GK38.TauGammaValueProbe

/-! Scalar and actual spectral regressions for the standard-root branch. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem stdRoot_total_collapse_probe38 (a : ℂ) :
    stdRoot38 a 0 a = 0 ∧ stdRoot38 a 0 (a + Complex.I) = -Complex.I := by
  constructor
  · simp [stdRoot_degenerate38]
  · rw [stdRoot_degenerate38]; ring

theorem stdRoot_wrong_principal_probe38 :
    stdRoot38 0 0 1 = -1 ∧ Complex.sqrt (((0 : ℂ) - 1) * (0 - 1)) = 1 := by
  simp [stdRoot_degenerate38]

theorem stdRoot_complex_orientation_probe38 :
    (1 / 2 : ℂ) ∉ segment ℝ (-Complex.I) Complex.I ∧
    stdRoot38 0 (-4) (1 / 2) ^ 2 = 5 / 4 ∧
    1 - ((-4 : ℂ) / 4) / (0 - (1 / 2 : ℂ))^2 ∈ Complex.slitPlane := by
  have hz : (1 / 2 : ℂ) ∉ segment ℝ (-Complex.I) Complex.I := by
    rintro ⟨u, v, _hu, _hv, _hs, he⟩
    have hr := congrArg Complex.re he
    norm_num [Complex.real_smul] at hr
  have hm : (-Complex.I + Complex.I) / 2 = (0 : ℂ) := by simp
  have hg : (Complex.I - -Complex.I)^2 = (-4 : ℂ) := by
    ring_nf
    norm_num [Complex.I_sq]
  refine ⟨hz, ?_, ?_⟩
  · have h := stdRoot_sq38 (-Complex.I) Complex.I (1 / 2) hz
    rw [hm, hg] at h
    rw [h]
    ring_nf
    norm_num [Complex.I_sq]
  · have h := (stdRoot_slit38 (-Complex.I) Complex.I (1 / 2) hz).2
    rw [hm, hg] at h
    exact h

theorem stdRoot_actual_nonfree_central_probe38 :
    stdRoot38 (tauN (realSlice (constL2 1)) 0)
      (gamma2 (realSlice (constL2 1)) 0) 2 ^ 2 = 3 := by
  have h := tauGamma_probe_nonfree_open_mean38
  rw [h.1, h.2.2, stdRoot_sq_of_ne38 (by norm_num : (0 : ℂ) - 2 ≠ 0)]
  norm_num

theorem stdRoot_actual_nonfree_negative_probe38 (z : ℂ) :
    stdRoot38 (tauN (realSlice (constL2 1)) (-1))
      (gamma2 (realSlice (constL2 1)) (-1)) z =
        (((-Real.sqrt (Real.pi ^ 2 + 1) : ℝ) : ℂ) - z) := by
  have h := tauGamma_probe_nonfree_negative_values38
  rw [h.1, h.2, stdRoot_degenerate38]

end
end NlsGge.GK38
