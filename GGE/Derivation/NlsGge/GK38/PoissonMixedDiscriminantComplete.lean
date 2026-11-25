import NlsGge.GK38.PoissonMixedDiscriminantKernel

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem discrim_joint_potential_partial38 (φ : PotPair) (z : ℂ) :
    (fderiv ℂ (fun p : PotPair × ℂ => discrim p.1 p.2) (φ,z)).comp
      potentialInclusion = gradDiscrimCLM φ z := by
  let f : PotPair × ℂ → ℂ := fun p => discrim p.1 p.2
  have hf : HasFDerivAt f (fderiv ℂ f (φ,z)) (φ,z) :=
    (analyticOnNhd_discrim (φ,z) (mem_univ _)).differentiableAt.hasFDerivAt
  have hg : HasFDerivAt (fun ψ : PotPair => (ψ,z)) potentialInclusion φ := by
    change HasFDerivAt (fun ψ : PotPair => (ψ,z)) (ContinuousLinearMap.inl ℂ PotPair ℂ) φ
    exact hasFDerivAt_prodMk_left (𝕜 := ℂ) φ z
  have hp := hf.comp φ hg
  change HasFDerivAt (fun ψ : PotPair => discrim ψ z)
    ((fderiv ℂ f (φ,z)).comp potentialInclusion) φ at hp
  exact hp.unique (hasFDerivAt_discrim z φ)

theorem continuous_discrimPoisson38 (φ : PotPair) (h : PairKernelCont38) :
    Continuous (fun z : ℂ => kernelPoisson38 (gradDiscrimCont38 φ z) h) := by
  let f : PotPair × ℂ → ℂ := fun p => discrim p.1 p.2
  have hD : Continuous (fderiv ℂ f) :=
    continuousOn_univ.mp ((analyticOnNhd_discrim.fderiv_of_isOpen isOpen_univ).continuousOn)
  have he : (fun z : ℂ => kernelPoisson38 (gradDiscrimCont38 φ z) h) =
      (fun z : ℂ => (fderiv ℂ f (φ,z)) (potentialInclusion (kernelHamField38 h))) := by
    funext z
    have hp := congrArg (fun L : PotPair →L[ℂ] ℂ => L (kernelHamField38 h))
      (discrim_joint_potential_partial38 φ z)
    exact (kernelPairingTarget (gradDiscrimCont38 φ z) h).2.2.symm.trans hp.symm
  rw [he]
  exact (hD.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const

theorem scalar_discrim_dirichlet38 (q d u e a b j : ℂ)
    (hd : d ≠ 0) (hu : u ≠ 0) (he : e ≠ 0)
    (hq : q=2*d*u) (hb : u^2-1=u*b)
    (h : -2*Complex.I*a*(u^2-1)=2*Complex.I*e*j) :
    2*(-q⁻¹*j)=b*(a/(e*d)) := by
  have hi : (2 : ℂ)*Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hj : j=(-a*(u^2-1))/e := by
    apply (eq_div_iff he).mpr
    apply mul_left_cancel₀ hi
    calc
      (2*Complex.I)*(j*e)=2*Complex.I*e*j := by ring
      _ = -2*Complex.I*a*(u^2-1) := h.symm
      _ = (2*Complex.I)*(-a*(u^2-1)) := by ring
  rw [hb] at hj
  rw [hq,hj]
  field_simp

theorem discrim_dirichlet_mixed_off_base38 (φ : PotPair) (z ζ : ℂ)
    (hr : dirichletChar φ z=0) (hs : deriv (dirichletChar φ) z ≠ 0) (hne : ζ ≠ z) :
    2*kernelPoisson38 (gradDiscrimCont38 φ ζ) (dirEigenKernel38 φ z) =
      antiDiscrim φ z*dirInterpolation38 φ z ζ := by
  have hU := normingFactor_ne_zero_at_dirichlet_root38 φ z hr
  have _hQ := dirichlet_Q_ne_zero φ z hr hs
  rw [dirInterpolation_off_root38 φ z ζ hr hne,discrim_dir_poisson_eq_weightedIntegral38]
  exact scalar_discrim_dirichlet38 _ _ _ _ _ _ _ hs hU (sub_ne_zero.mpr hne)
    (norming_Q_at_dirichlet_root38 φ z hr) (norming_anti_at_dirichlet_root38 φ z hr)
    (weightedColumnDir_integral_identity38 φ z ζ hr)

theorem discriminantDirichletMixedTarget : DiscriminantDirichletMixedTarget := by
  intro φ z ζ hr hs
  refine ⟨dirichlet_Q_ne_zero φ z hr hs,?_⟩
  by_cases he : ζ=z
  · subst ζ
    let L : ℂ → ℂ := fun w => 2*kernelPoisson38 (gradDiscrimCont38 φ w) (dirEigenKernel38 φ z)
    let R : ℂ → ℂ := fun w => antiDiscrim φ z*dirInterpolation38 φ z w
    have hL : Continuous L := continuous_const.mul (continuous_discrimPoisson38 φ _)
    have hR : Continuous R := continuous_const.mul
      (continuousOn_univ.mp (dirichletInterpolationTarget φ z hr hs).1.continuousOn)
    have hEq : L =ᶠ[𝓝[≠] z] R := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact discrim_dirichlet_mixed_off_base38 φ z w hr hs hw
    exact tendsto_nhds_unique
      (hL.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hEq.symm)
  · exact discrim_dirichlet_mixed_off_base38 φ z ζ hr hs he

theorem periodicDirichletMixedTarget : PeriodicDirichletMixedTarget := by
  intro φ ζ z _hp hs hr hsr
  have hd := periodic_simple_discrim_nonzero φ ζ hs
  refine ⟨hd,?_⟩
  rw [periodicKernel38,kernelPoisson_smul_left38]
  calc
    2*(-(deriv (discrim φ) ζ)⁻¹*kernelPoisson38 (gradDiscrimCont38 φ ζ) (dirEigenKernel38 φ z)) =
      -(2*kernelPoisson38 (gradDiscrimCont38 φ ζ) (dirEigenKernel38 φ z))/deriv (discrim φ) ζ := by
      rw [div_eq_mul_inv]
      ring
    _ = _ := by rw [(discriminantDirichletMixedTarget φ z ζ hr hsr).2]

end
end NlsGge.GK38.PoissonMixed38
