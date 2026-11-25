import NlsGge.GK38.AbelianJacobianGeometry

/-! Exact source diagonal quotient after finite-factor differentiation.
UNCOMPILED source preparation; no own-gap division occurs. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot
namespace NlsGge.GK38.P3JacobianColumns
noncomputable section

theorem column_diagonal_div_root (n m : ℤ) (hmn : m ≠ n)
    (s : Lib.L2Seq) (φ : PotPair) (z : ℂ) (hp : (φ,z) ∈ rootDomain38)
    (hsn : Lib.sigmaOf s n-z ≠ 0) :
    p3NumeratorColumn38 n m s z / canonRoot38 φ z =
      Complex.I * p2OmittedRatio38 m ((φ,s),z) / (Lib.sigmaOf s n-z) /
        stdRoot38 (tauN φ m) (gamma2 φ m) z := by
  let s' : Lib.L2Seq := s + (1 : ℂ) • lp.single 2 m (1 : ℂ)
  have hn : Lib.sigmaOf s' n = Lib.sigmaOf s n := by
    simp only [s', Lib.sigmaOf, lp.coeFn_add, Pi.add_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 m (1 : ℂ) (Ne.symm hmn),
      mul_zero, add_zero]
  have hm : Lib.sigmaOf s' m = Lib.sigmaOf s m + 1 := by
    simp only [s', Lib.sigmaOf, lp.coeFn_add, Pi.add_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply_self, one_mul]
    ring
  have hr : p2OmittedRatio38 m ((φ,s'),z) = p2OmittedRatio38 m ((φ,s),z) := by
    unfold p2OmittedRatio38
    rw [Lib.omitProd_add_single]
  have hline := numerator_add_single n m hmn s z 1
  have hh : p3NumeratorColumn38 n m s z =
      p2FullNumerator38 n s' z-p2FullNumerator38 n s z := by
    dsimp [s']
    linear_combination -hline
  have hq0 := p2FullNumerator_div_root38 n m s φ z hp hsn
  have hq1 := p2FullNumerator_div_root38 n m s' φ z hp (by simpa only [hn] using hsn)
  rw [hh, sub_div, hq1, hq0, hn, hm, hr]
  ring

theorem weighted_column_diagonal_integrand (n m : ℤ) (hmn : m ≠ n)
    (s : Lib.L2Seq) (φ : PotPair) (z : ℂ) (hp : (φ,z) ∈ rootDomain38)
    (hsn : Lib.sigmaOf s n-z ≠ 0) :
    (((n-m : ℤ) : ℂ)) * (p3NumeratorColumn38 n m s z / canonRoot38 φ z) =
      Complex.I * p3DiagonalFactor38 n m φ s z /
        stdRoot38 (tauN φ m) (gamma2 φ m) z := by
  rw [column_diagonal_div_root n m hmn s φ z hp hsn]
  unfold p3DiagonalFactor38
  ring

theorem diagonalFactor_real (u : PhysicalL2) (s : Lib.L2Seq)
    (hs : ∀ k : ℤ, (s k).im = 0) (n m : ℤ) (x : ℝ)
    (hp : (realSlice u,(x : ℂ)) ∈ a5OmittedRootDomain38 m) :
    (p3DiagonalFactor38 n m (realSlice u) s (x : ℂ)).im = 0 := by
  have hR := omittedRatio_real u s hs m x hp
  have hn : (Lib.sigmaOf s n-(x : ℂ)).im = 0 := by
    simp only [Lib.sigmaOf, Complex.sub_im, Complex.add_im,
      Complex.mul_im, Complex.intCast_im, Complex.ofReal_im, hs n,
      mul_zero, zero_mul, add_zero, sub_zero]
  unfold p3DiagonalFactor38
  simp only [Complex.div_im, Complex.mul_im, Complex.intCast_im,
    hR, hn, mul_zero, zero_mul, add_zero, sub_zero, zero_div]

end
end NlsGge.GK38.P3JacobianColumns
