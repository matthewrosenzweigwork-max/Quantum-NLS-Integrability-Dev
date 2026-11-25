import NlsGge.GK38.XiSqScalarKernelBound
import NlsGge.GK38.XiSqUniformSmallness

set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

/-- The GLOBAL principal-root estimate applies before any slit-domain reasoning. -/
theorem a5BoundaryQ_error_bound38 (n : ℤ) (p : PotPair × ℂ) (d : ℝ)
    (hd : 0 < d) (hw : d ≤ ‖tauN p.1 n-p.2‖) :
    ‖a5BoundaryQ38 n p-1‖ ≤ ‖gamma2 p.1 n‖/(4*d^2) := by
  have h := Lib.norm_sqrt_one_sub_sub_one_le
    ((gamma2 p.1 n/4)/(tauN p.1 n-p.2)^2)
  change ‖a5BoundaryQ38 n p-1‖ ≤ _ at h
  apply h.trans
  rw [Complex.norm_div, Complex.norm_div, norm_pow]
  norm_num only [Complex.norm_ofNat]
  rw [div_div]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
  nlinarith [norm_nonneg (tauN p.1 n-p.2)]

/-- The actual centered kernel has a uniform linear error bound against the free Cauchy kernel.
No noncollapsed-gap hypothesis occurs: the critical displacement is earned by the actual D4 identity. -/
theorem a5ActualCenteredKernel_error38 (φ : PotPair) (n : ℤ) (z c : ℂ)
    (hp : (φ,z) ∈ rootDomain38) (d r : ℝ) (hd : 0 < d) (hr : 0 < r)
    (hw : d ≤ ‖tauN φ n-z‖) (hw₀ : r ≤ ‖c-z‖)
    (hcrit : ‖lamDot φ n-tauN φ n‖ ≤ 1)
    (hgap : ‖gamma2 φ n‖/(4*d^2) ≤ (1/2:ℝ)) :
    ‖a5CenteredKernel38 n (φ,z)-(-1/(8*Complex.I*(c-z)))‖ ≤
      (1/(8*d)) * (4*(1+1/d)*‖a5Chi38 n (φ,z)-1‖ +
        8*(1+1/d)*(‖gamma2 φ n‖/(4*d^2)) + ‖lamDot φ n-tauN φ n‖/d) +
        ‖tauN φ n-c‖/(8*d*r) := by
  have hqerr := a5BoundaryQ_error_bound38 n (φ,z) d hd hw
  have hqsmall : ‖a5BoundaryQ38 n (φ,z)-1‖ ≤ (1/2:ℝ) := hqerr.trans hgap
  have hqlo : (1/2:ℝ) ≤ ‖a5BoundaryQ38 n (φ,z)‖ := by
    have htri := norm_le_norm_sub_add (1:ℂ) (a5BoundaryQ38 n (φ,z))
    rw [norm_one,norm_sub_rev] at htri
    linarith
  have hqup : ‖a5BoundaryQ38 n (φ,z)‖ ≤ 2 := by
    have htri := norm_le_norm_sub_add (a5BoundaryQ38 n (φ,z)) (1:ℂ)
    rw [norm_one] at htri
    linarith
  have hplus : 1 ≤ ‖1+a5BoundaryQ38 n (φ,z)‖ := by
    have hre := Lib.re_sqrt_nonneg
      (1-(gamma2 φ n/4)/(tauN φ n-z)^2)
    change 0 ≤ (a5BoundaryQ38 n (φ,z)).re at hre
    have hb := Complex.re_le_norm (1+a5BoundaryQ38 n (φ,z))
    simp only [Complex.add_re,Complex.one_re] at hb
    linarith
  have h := a5CenteredScalar_error38 (a5Chi38 n (φ,z))
    (tauN φ n-z) (c-z) (lamDot φ n-tauN φ n) (a5BoundaryQ38 n (φ,z))
    d r hd hr hw hw₀ hcrit hqlo hqup hplus
  have hident : a5CenteredKernel38 n (φ,z) =
      -(a5Chi38 n (φ,z)/Complex.I)*
        ((tauN φ n-z)+(lamDot φ n-tauN φ n))/
        (4*(tauN φ n-z)^2*a5BoundaryQ38 n (φ,z)*(1+a5BoundaryQ38 n (φ,z))) := by
    unfold a5CenteredKernel38 a5CenteredAnalyticTerm38
    rw [← a5CriticalA_identity38 n φ hp.1]
  rw [← hident] at h
  have he : (tauN φ n-z)-(c-z) = tauN φ n-c := by ring
  rw [he] at h
  apply h.trans
  have hfac : 0 ≤ 8*(1+1/d) := by positivity
  have hscale : 0 ≤ 1/(8*d) := by positivity
  exact add_le_add (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hqerr hfac)) le_rfl) hscale) le_rfl

end
end NlsGge.GK38
