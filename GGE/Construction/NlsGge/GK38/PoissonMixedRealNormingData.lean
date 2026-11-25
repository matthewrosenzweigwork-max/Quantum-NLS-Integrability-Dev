import NlsGge.GK38.PoissonMixedPeriodicBasic
import NlsGge.GK38.GradEigenRealPeriodicLabels

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem normingFactor_real_star38 (u : PhysicalL2) (x : ℝ) :
    star (normingFactor (realSlice u) (x : ℂ)) = normingFactor (realSlice u) (x : ℂ) := by
  simp only [normingFactor,star_div₀,star_add,star_ofNat,monodromyPair_real_entry_star38]
  change (monodromyPair (realSlice u) (x : ℂ) 1 1 +
    monodromyPair (realSlice u) (x : ℂ) 1 0 +
    monodromyPair (realSlice u) (x : ℂ) 0 1 +
    monodromyPair (realSlice u) (x : ℂ) 0 0)/2 = _
  ring

theorem normingFactor_real_im38 (u : PhysicalL2) (x : ℝ) :
    (normingFactor (realSlice u) (x : ℂ)).im = 0 := by
  have h := congrArg Complex.im (normingFactor_real_star38 u x)
  change -(normingFactor (realSlice u) (x : ℂ)).im =
    (normingFactor (realSlice u) (x : ℂ)).im at h
  linarith

theorem norming_trace_polynomial38 (φ : PotPair) (z : ℂ)
    (hr : dirichletChar φ z = 0) :
    (normingFactor φ z)^2+1 = discrim φ z * normingFactor φ z := by
  have hi := dirichlet_amplitude_inverse φ z hr
  rw [normingFactor_at_dirichlet_root38 φ z hr,discrim_eq]
  linear_combination -hi

theorem scalar_signed_norming_positive38 (p u d : ℝ)
    (hp : p^2=1) (hd : 2 ≤ p*d) (hu : u^2+1=d*u) : 0 < p*u := by
  have hpoly : (p*u)^2+1=(p*d)*(p*u) := by
    calc
      (p*u)^2+1=p^2*(u^2+1) := by rw [mul_pow,hp]; ring
      _=p^2*(d*u) := by rw [hu]
      _=(p*d)*(p*u) := by ring
  by_contra hn
  have hs : p*u ≤ 0 := le_of_not_gt hn
  have hm : (p*d)*(p*u) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hs
  nlinarith [sq_nonneg (p*u)]

theorem signedNorming_positive38 (u : PhysicalL2) (n : ℤ) :
    0 < signedNorming38 u n := by
  have hU := normingFactor_real_im38 u (gkMu u n)
  have hpoly := congrArg Complex.re
    (norming_trace_polynomial38 (realSlice u) (gkMu u n : ℂ) (gkMu_root38 u n))
  have hcos : (parity n).re=Real.cos ((n : ℝ)*Real.pi) := by
    have hc : (Real.cos ((n : ℝ)*Real.pi) : ℂ) = parity n := by
      rw [Real.cos_int_mul_pi]
      simp [parity]
    exact (congrArg Complex.re hc).symm
  have hval : signedNorming38 u n = (parity n).re *
      (normingFactor (realSlice u) (gkMu u n : ℂ)).re := by
    simp only [signedNorming38,Complex.mul_re,hU,mul_zero,sub_zero]
  rw [hval,hcos]
  apply scalar_signed_norming_positive38 _ _ _ (real_cos_int_mul_pi_sq_E02_38 n)
    (dirichlet_discriminant_sign38 u n)
  simpa only [Complex.add_re,Complex.one_re,Complex.mul_re,hU,
    mul_zero,sub_zero,pow_two] using hpoly

end
end NlsGge.GK38.PoissonMixed38
