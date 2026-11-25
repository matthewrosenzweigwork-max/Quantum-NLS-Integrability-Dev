import NlsGge.GK38.PoissonMixedRealKappaAnalytic

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem actual_realKappa_derivative_hamField38 (u : PhysicalL2) (n : ℤ)
    (h : PairKernelCont38) (hsym : realSymmetric h) :
    (fderiv ℝ (fun v : PhysicalL2 => realKappa38 v n) u) (kernelHamField38 h).1 =
      (kernelPoisson38 (kappaKernel38 (realSlice u) (gkMu u n : ℂ)) h).re := by
  have hreal := kernelHamField_realSlice38 h hsym
  rw [(hasFDerivAt_realKappa38 u n).fderiv]
  change (kappaCLM38 (realSlice u) (gkMu u n : ℂ) (realSlice (kernelHamField38 h).1)).re = _
  rw [hreal]
  exact congrArg Complex.re
    (kernelPairingTarget (kappaKernel38 (realSlice u) (gkMu u n : ℂ)) h).2.2

theorem actual_mu_derivative_kernelHamField38 (u : PhysicalL2) (n : ℤ)
    (h : PairKernelCont38) (hsym : realSymmetric h) :
    (fderiv ℝ (fun v : PhysicalL2 => gkMu v n) u) (kernelHamField38 h).1 =
      (kernelPoisson38 (dirEigenKernel38 (realSlice u) (gkMu u n : ℂ)) h).re := by
  have hd := actual_dirichlet_label_complex_gradient u n (kernelHamField38 h).1
  rw [kernelHamField_realSlice38 h hsym,
    dirImplicitGradient_eq_kernel38 _ _ (gkMu_root38 u n)
      (dirichlet_root_deriv_ne_zero38 u (gkMu u n) (gkMu_root38 u n))] at hd
  rw [(kernelPairingTarget (dirEigenKernel38 (realSlice u) (gkMu u n : ℂ)) h).2.2] at hd
  exact (congrArg Complex.re hd).symm.symm

theorem realCanonicalKappaBracketsTarget : RealCanonicalKappaBracketsTarget := by
  intro u m n
  have h := complexKappaBracketsTarget (realSlice u) (gkMu u m : ℂ) (gkMu u n : ℂ)
    (gkMu_root38 u m) (gkMu_root38 u n)
    (dirichlet_root_deriv_ne_zero38 u (gkMu u m) (gkMu_root38 u m))
    (dirichlet_root_deriv_ne_zero38 u (gkMu u n) (gkMu_root38 u n))
  have heq : ((gkMu u m : ℂ)=(gkMu u n : ℂ)) ↔ m=n := by
    constructor
    · intro hv
      exact gkMu_injective38 u (Complex.ofReal_injective hv)
    · rintro rfl
      rfl
  simp only [heq] at h
  have hA := h.2.2.2.2.1
  have hB := h.2.2.2.2.2.1
  have hC := h.2.2.2.2.2.2
  refine ⟨hA,hB,hC,?_,?_,?_⟩
  · rw [actual_realKappa_derivative_hamField38 u m _ (dirEigenKernel38_realSymmetric u n)]
    simpa only [apply_ite,Complex.one_re,Complex.zero_re] using congrArg Complex.re hA
  · rw [actual_mu_derivative_kernelHamField38 u m _ (kappaKernel_realSymmetric38 u n)]
    simpa only [apply_ite,Complex.neg_re,Complex.one_re,Complex.zero_re] using congrArg Complex.re hB
  · rw [actual_realKappa_derivative_hamField38 u m _ (kappaKernel_realSymmetric38 u n),hC,Complex.zero_re]

end
end NlsGge.GK38.PoissonMixed38
