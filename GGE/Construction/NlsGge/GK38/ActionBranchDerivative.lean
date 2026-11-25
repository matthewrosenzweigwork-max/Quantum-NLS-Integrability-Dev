import NlsGge.GK38.ActionBranchUpper

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
namespace NlsGge.GK38.ActionBranch
noncomputable section

theorem discrim_hasDeriv_upper (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (discrim (realSlice u))
      (-2 * Complex.sin (actualQuasimomentumE02_38 u z) *
        deriv (actualQuasimomentumE02_38 u) z) z := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  have hd : HasDerivAt (actualQuasimomentumE02_38 u)
      (deriv (actualQuasimomentumE02_38 u) z) z :=
    (hk.1 z hz).differentiableAt.hasDerivAt
  have hc := ((Complex.hasDerivAt_cos (actualQuasimomentumE02_38 u z)).comp z hd).const_mul
    (2 : ℂ)
  have he : discrim (realSlice u) =ᶠ[𝓝 z]
      (fun w : ℂ => 2 * Complex.cos (actualQuasimomentumE02_38 u w)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
    exact (discrim_realSlice u w).trans (congrArg (fun c : ℂ => 2 * c) (hk.2.1 w hw).symm)
  exact (hc.congr_of_eventuallyEq he).congr_deriv (by ring)

theorem discrim_deriv_div_root_upper (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z =
      -Complex.I * deriv (actualQuasimomentumE02_38 u) z := by
  have hroot := canonRoot_ne_zero38 (realSlice u) (realSlice_mem_gkW u) z
    (root_domain u z hz).2
  have hd := discrim_hasDeriv_upper u z hz
  rw [hd.deriv]
  apply (div_eq_iff hroot).2
  rw [canonical_root_upper u z hz]
  calc
    -2 * Complex.sin (actualQuasimomentumE02_38 u z) *
        deriv (actualQuasimomentumE02_38 u) z =
        (2 * Complex.I ^ 2) * (Complex.sin (actualQuasimomentumE02_38 u z) *
          deriv (actualQuasimomentumE02_38 u) z) := by rw [Complex.I_sq]; ring
    _ = _ := by ring

theorem primitive_hasDeriv_upper (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (fun w : ℂ => -Complex.I * actualQuasimomentumE02_38 u w)
      (deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z) z := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  have hd := (hk.1 z hz).differentiableAt.hasDerivAt.const_mul (-Complex.I)
  exact hd.congr_deriv (discrim_deriv_div_root_upper u z hz).symm

theorem actionIntegrand_upper (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    actionIntegrand38 (realSlice u) z =
      z * (-Complex.I * deriv (actualQuasimomentumE02_38 u) z) := by
  unfold actionIntegrand38
  rw [mul_div_assoc, discrim_deriv_div_root_upper u z hz]

end
end NlsGge.GK38.ActionBranch
