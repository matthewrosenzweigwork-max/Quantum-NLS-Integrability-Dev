import NlsGge.GK38.GradEigenDirichletSpectral
import NlsGge.GK38.GradEigenBranch

set_option autoImplicit false
open Set Filter Topology MeasureTheory
namespace NlsGge.GK38.GradEigen38
noncomputable section
theorem integralPairCLM38_kernelSub (g k : PairKernelCont38) (t : Time) :
    integralPairCLM38 (g-k) t = integralPairCLM38 g t - integralPairCLM38 k t := by
  apply ContinuousLinearMap.ext
  intro h
  change pairIntegral38 (g-k) t h = pairIntegral38 g t h - pairIntegral38 k t h
  unfold pairIntegral38
  rw [← intervalIntegral.integral_sub (intervalIntegrable_pairKernel38 g t h)
    (intervalIntegrable_pairKernel38 k t h)]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using (uIcc_zero_subset t.2) hs
  simp only [pairKernelExt38_of_mem _ hs',ContinuousMap.sub_apply,Pi.sub_apply]
  ring

theorem dirichlet_CLM_at_root (φ : PotPair) (z : ℂ) (hroot : dirichletChar φ z = 0) :
    dirCLM φ z = (-(monodromyPair φ z 1 1 - monodromyPair φ z 0 1)/2) •
      integralPairCLM38 (square (state φ z (![1,1] : PairVec38))) t1 := by
  unfold dirCLM fundamentalEntryCLM38
  rw [← integralPairCLM38_kernelAdd, ← integralPairCLM38_kernelSub,
    ← integralPairCLM38_kernelSub, dirichlet_entry_kernel_at_root φ z hroot,
    integralPairCLM38_kernelSmul,smul_smul]
  have hc : (2*Complex.I)⁻¹ * (-Complex.I *
      (monodromyPair φ z 1 1 - monodromyPair φ z 0 1)) =
      -(monodromyPair φ z 1 1 - monodromyPair φ z 0 1)/2 := by
    field_simp <;> ring
  rw [hc]

theorem dirichlet_Q_spectral_relation (φ : PotPair) (z : ℂ)
    (hroot : dirichletChar φ z = 0) :
    (monodromyPair φ z 1 1 - monodromyPair φ z 0 1) *
      Q (state φ z (![1,1] : PairVec38)) = 2 * deriv (dirichletChar φ) z := by
  have hd := (hasDerivAt_dirichlet_spectral φ z).deriv
  rw [dirichlet_spectral_Q φ z hroot] at hd
  linear_combination -2*hd

theorem dirichlet_Q_ne_zero (φ : PotPair) (z : ℂ) (hroot : dirichletChar φ z = 0)
    (hsimple : deriv (dirichletChar φ) z ≠ 0) :
    Q (state φ z (![1,1] : PairVec38)) ≠ 0 := by
  intro hQ
  have hd := dirichlet_Q_spectral_relation φ z hroot
  rw [hQ,mul_zero] at hd
  apply hsimple
  linear_combination -hd/2

theorem scalar_inverse_root_gradient (q r d : ℂ) (hq : q ≠ 0) (hd : d ≠ 0)
    (hrel : r*q = 2*d) : -d⁻¹*(-r/2) = q⁻¹ := by
  field_simp
  linear_combination hrel

theorem complex_dirichlet_gradient_identity (φ : PotPair) (z : ℂ)
    (hroot : dirichletChar φ z = 0) (hsimple : deriv (dirichletChar φ) z ≠ 0) :
    dirImplicitGradient φ z = bilinearGradient (state φ z (![1,1] : PairVec38)) := by
  have hQ := dirichlet_Q_ne_zero φ z hroot hsimple
  have hrel := dirichlet_Q_spectral_relation φ z hroot
  unfold dirImplicitGradient bilinearGradient
  rw [dirichlet_CLM_at_root φ z hroot,smul_smul,
    scalar_inverse_root_gradient _ _ _ hQ hsimple hrel]

theorem dirichlet_joint_potential_partial (φ : PotPair) (z : ℂ) :
    (fderiv ℂ (fun p : PotPair × ℂ => dirichletChar p.1 p.2) (φ,z)).comp
      potentialInclusion = dirCLM φ z := by
  let f : PotPair × ℂ → ℂ := fun p => dirichletChar p.1 p.2
  have hf : HasFDerivAt f (fderiv ℂ f (φ,z)) (φ,z) :=
    (analyticOnNhd_dirichletChar (φ,z) (mem_univ _)).differentiableAt.hasFDerivAt
  have hcurve : HasFDerivAt (fun ψ : PotPair => (ψ,z)) potentialInclusion φ := by
    change HasFDerivAt (fun ψ : PotPair => (ψ,z)) (ContinuousLinearMap.inl ℂ PotPair ℂ) φ
    exact hasFDerivAt_prodMk_left (𝕜 := ℂ) φ z
  have hp := hf.comp φ hcurve
  change HasFDerivAt (fun ψ : PotPair => dirichletChar ψ z)
    ((fderiv ℂ f (φ,z)).comp potentialInclusion) φ at hp
  exact hp.unique (dirichlet_characteristic_derivative φ z)

theorem dirichlet_joint_spectral_partial (φ : PotPair) (z : ℂ) :
    (fderiv ℂ (fun p : PotPair × ℂ => dirichletChar p.1 p.2) (φ,z)) (0,1) =
      deriv (dirichletChar φ) z := by
  have hf := (analyticOnNhd_dirichletChar (φ,z) (mem_univ _)).differentiableAt.hasFDerivAt
  have hcurve : HasDerivAt (fun w : ℂ => (φ,w)) ((0 : PotPair),(1 : ℂ)) z :=
    (hasDerivAt_const z φ).prodMk (hasDerivAt_id z)
  have hs : HasDerivAt (dirichletChar φ)
      ((fderiv ℂ (fun p : PotPair × ℂ => dirichletChar p.1 p.2) (φ,z)) (0,1)) z :=
    hf.comp_hasDerivAt z hcurve
  exact hs.deriv.symm

/-- Canonical complex Dirichlet gradient; no reality or H¹ restriction. -/
def ComplexDirichletSimpleTarget : Prop :=
  ∀ (φ : PotPair) (z : ℂ),
    dirichletChar φ z = 0 → deriv (dirichletChar φ) z ≠ 0 →
    Q (state φ z (![1,1] : PairVec38)) ≠ 0 ∧
    dirImplicitGradient φ z = bilinearGradient (state φ z (![1,1] : PairVec38)) ∧
    ∃ (U : Set PotPair) (κ : PotPair → ℂ),
      IsOpen U ∧ φ ∈ U ∧ AnalyticOnNhd ℂ κ U ∧ κ φ = z ∧
      (∀ ψ ∈ U, dirichletChar ψ (κ ψ) = 0) ∧
      HasFDerivAt κ (bilinearGradient (state φ z (![1,1] : PairVec38))) φ



theorem complex_dirichlet_simple_target : ComplexDirichletSimpleTarget := by
  intro φ z hroot hsimple
  have hQ := dirichlet_Q_ne_zero φ z hroot hsimple
  have hgrad := complex_dirichlet_gradient_identity φ z hroot hsimple
  have hc : (fderiv ℂ (fun p : PotPair × ℂ => dirichletChar p.1 p.2) (φ,z)) (0,1) ≠ 0 := by
    rw [dirichlet_joint_spectral_partial]
    exact hsimple
  obtain ⟨U,κ,hU,hbase,hκ,hvalue,heq,hder⟩ :=
    simple_root_branch_target (fun p : PotPair × ℂ => dirichletChar p.1 p.2) φ z
      (analyticOnNhd_dirichletChar (φ,z) (mem_univ _)) hroot hc
  refine ⟨hQ,hgrad,U,κ,hU,hbase,hκ,hvalue,heq,?_⟩
  rw [dirichlet_joint_potential_partial,dirichlet_joint_spectral_partial] at hder
  change HasFDerivAt κ (dirImplicitGradient φ z) φ at hder
  rw [hgrad] at hder
  exact hder

theorem bilinear_gradient_smul (c : ℂ) (w : PairKernelCont38)
    (hc : c ≠ 0) (_hw : Q w ≠ 0) : bilinearGradient (c • w) = bilinearGradient w := by
  have hs : (c^2 * Q w)⁻¹ * c^2 = (Q w)⁻¹ := by
    field_simp
  unfold bilinearGradient
  rw [Q_smul,square_smul,integralPairCLM38_kernelSmul,smul_smul,hs]


end
end NlsGge.GK38.GradEigen38
