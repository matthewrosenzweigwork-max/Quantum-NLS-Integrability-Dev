import NlsGge.GK38.GradEigenClosedKernelAlgebra
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem actual_deltaMu_hasFDerivAt (u : PhysicalL2) (n : ℤ) :
    HasFDerivAt (fun v : PhysicalL2 => deltaMu v n) (realKernelCLM (closedKernel2 u n)) u := by
  let dr := realEnergyGradient (dirState u n)
  let f : PotPair × ℂ → ℂ := fun p => antiDiscrim p.1 p.2
  let D := fderiv ℂ f (realSlice u,(gkMu u n : ℂ))
  let A := spectralAntiDiscrimIntegral38 (realSlice u) (gkMu u n : ℂ)
  have hmu : HasFDerivAt (fun v : PhysicalL2 => gkMu v n) dr u :=
    actual_dirichlet_label_hasFDerivAt u n
  have hf : HasFDerivAt f D (realSlice u,(gkMu u n : ℂ)) :=
    (analyticOnNhd_antiDiscrim (realSlice u,(gkMu u n : ℂ)) (mem_univ _)).differentiableAt.hasFDerivAt
  have hgraph : HasFDerivAt (fun v : PhysicalL2 => (realSlice v,(gkMu v n : ℂ)))
      (realSlice.prod (Complex.ofRealCLM.comp dr)) u :=
    realSlice.hasFDerivAt.prodMk (Complex.ofRealCLM.hasFDerivAt.comp u hmu)
  have hd := Complex.reCLM.hasFDerivAt.comp u ((hf.restrictScalars ℝ).comp u hgraph)
  have hA : (A.re : ℂ)=A := by
    apply Complex.ext
    · rfl
    · exact (spectralAnti_real u (gkMu u n)).symm
  have hkernel : realKernelCLM (closedKernel2 u n)=
      A.re • realKernelCLM (normalizedSquare (dirState u n))+
        realKernelCLM (gradAntiDiscrimCont38 (realSlice u) (gkMu u n : ℂ)) := by
    change realKernelCLM (A • normalizedSquare (dirState u n)+_)=_
    rw [← hA,realKernelCLM_add,realKernelCLM_real_smul]
    rfl
  have heq : (Complex.reCLM.comp (D.restrictScalars ℝ)).comp
      (realSlice.prod (Complex.ofRealCLM.comp dr))=realKernelCLM (closedKernel2 u n) := by
    ext h
    have hp : D (realSlice h,0)=gradAntiDiscrimCLM (realSlice u) (gkMu u n : ℂ) (realSlice h) :=
      congrArg (fun L : PotPair →L[ℂ] ℂ => L (realSlice h))
        (anti_joint_potential_partial (realSlice u) (gkMu u n : ℂ))
    have hs : D (0,1)=A := anti_joint_spectral_partial (realSlice u) (gkMu u n : ℂ)
    have hdecomp : D (realSlice h,(dr h : ℂ))=
        gradAntiDiscrimCLM (realSlice u) (gkMu u n : ℂ) (realSlice h)+(dr h : ℂ)*A := by
      calc
        D (realSlice h,(dr h : ℂ))=D ((realSlice h,0)+(dr h : ℂ) • (0,1)) := by
          congr 1
          simp
        _ = D (realSlice h,0)+(dr h : ℂ)*D (0,1) := by rw [map_add,map_smul]; rfl
        _ = _ := by rw [hp,hs]
    rw [hkernel,← realEnergyGradient_eq_realKernel]
    change (D (realSlice h,(dr h : ℂ))).re=
      A.re*dr h+(gradAntiDiscrimCLM (realSlice u) (gkMu u n : ℂ) (realSlice h)).re
    rw [hdecomp]
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  change HasFDerivAt (fun v : PhysicalL2 => deltaMu v n)
    ((Complex.reCLM.comp (D.restrictScalars ℝ)).comp
      (realSlice.prod (Complex.ofRealCLM.comp dr))) u at hd
  rw [heq] at hd
  exact hd

def ClosedDerivativeKernelsTarget : Prop :=
  ∀ (u : PhysicalL2) (n : ℤ),
    HasFDerivAt (closedEquations n)
      ((realKernelCLM (closedKernel1 u n)).prod (realKernelCLM (closedKernel2 u n))) u

theorem closed_derivative_kernels_target : ClosedDerivativeKernelsTarget := by
  intro u n
  have hfirst := (actual_dirichlet_label_hasFDerivAt u n).sub (actual_neumann_label_hasFDerivAt u n)
  rw [realEnergyGradient_eq_realKernel,realEnergyGradient_eq_realKernel,
    ← realKernelCLM_sub] at hfirst
  exact hfirst.prodMk (actual_deltaMu_hasFDerivAt u n)

end
end NlsGge.GK38.GradEigen38
