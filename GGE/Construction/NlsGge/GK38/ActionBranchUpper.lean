import NlsGge.GK38.ActionBranchContinuity

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
namespace NlsGge.GK38.ActionBranch
noncomputable section

theorem rho_norm_lt_one (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    ‖rho u z‖ < 1 := by
  have hc := (continuous_rho_ray u z hz).norm
  have h0 : ‖rho ((0 : ℝ) • u) z‖ < 1 := by
    rw [zero_smul, rho_free z hz]
    exact exp_norm_lt_one z hz
  by_contra hn
  have h1 : 1 ≤ ‖rho ((1 : ℝ) • u) z‖ := by simpa only [one_smul] using not_lt.mp hn
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc (zero_le_one : (0 : ℝ) ≤ 1)
    hc.continuousOn (show (1 : ℝ) ∈ Icc ‖rho ((0 : ℝ) • u) z‖
      ‖rho ((1 : ℝ) • u) z‖ from ⟨h0.le, h1⟩)
  exact rho_norm_ne_one (t • u) z hz ht

theorem rho_eq_expRoot (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    rho u z = expRoot u z :=
  quadratic_unit_disc_unique _ _ _ (rho_quadratic u z hz) (expRoot_quadratic u z hz)
    (rho_norm_lt_one u z hz) (expRoot_norm_lt_one u z hz)

theorem canonical_root_upper (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    canonRoot38 (realSlice u) z =
      -2 * Complex.I * Complex.sin (actualQuasimomentumE02_38 u z) := by
  have h := rho_eq_expRoot u z hz
  have hk := (isActualQuasimomentumBranch_actualQuasimomentumE02_38 u).2.1 z hz
  unfold rho expRoot at h
  rw [Complex.exp_mul_I, discrim_realSlice, ← hk] at h
  linear_combination -2 * h

end
end NlsGge.GK38.ActionBranch
