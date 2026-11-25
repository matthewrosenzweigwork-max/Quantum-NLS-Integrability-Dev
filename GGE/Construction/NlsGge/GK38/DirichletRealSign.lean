import NlsGge.GK38.DirichletRealGapIndex

/-! The signed full discriminant at the canonical same-gap Dirichlet root. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem dirichlet_cos_real38 (w : ℂ) : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im := by
  conv_lhs => rw [← Complex.re_add_im w]
  rw [Complex.cos_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero]

theorem dirichlet_discriminant_sign38 (u : PhysicalL2) (n : ℤ) :
    2 ≤ Real.cos ((n : ℝ) * Real.pi) * (discrim (realSlice u) (gkMu u n : ℂ)).re := by
  have hlevel : actualQuasimomentumRealPartE02_38 u (gkMu u n) = (n : ℝ) * Real.pi := by
    have hmem := gkMu_mem_gap38 u n
    rw [← (actualGapLevelSet_eq_Icc_E02_38 u n).2] at hmem
    exact hmem
  have hre := dirichlet_cos_real38 (actualQuasimomentumBoundaryE02_38 u (gkMu u n))
  change (actualQuasimomentumBoundaryE02_38 u (gkMu u n)).re = _ at hlevel
  rw [actualQuasimomentumBoundaryE02_38_cos, hlevel] at hre
  rw [discrim_realSlice]
  norm_num [Complex.mul_re]
  rw [hre]
  have hs := real_cos_int_mul_pi_sq_E02_38 n
  have hp := Real.one_le_cosh (actualQuasimomentumBoundaryE02_38 u (gkMu u n)).im
  nlinarith

end
end NlsGge.GK38
