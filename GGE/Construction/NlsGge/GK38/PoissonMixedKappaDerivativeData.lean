import NlsGge.GK38.PoissonMixedComplexKappaBrackets

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem hasFDerivAt_norming_graph38 (φ : PotPair) (z : ℂ) (ρ : PotPair → ℂ)
    (L : PotPair →L[ℂ] ℂ) (hv : ρ φ = z) (hρ : HasFDerivAt ρ L φ) :
    HasFDerivAt (fun ψ : PotPair => normingFactor ψ (ρ ψ))
      (normingSpectral38 φ z • L + normingCLM38 φ z) φ := by
  let f : PotPair × ℂ → ℂ := fun p => normingFactor p.1 p.2
  let D := fderiv ℂ f (φ,z)
  have hf : HasFDerivAt f D (φ,ρ φ) := by
    rw [hv]
    exact (analyticOnNhd_normingFactor38 (φ,z) (mem_univ _)).differentiableAt.hasFDerivAt
  have hgraph := (hasFDerivAt_id φ).prodMk hρ
  have h := hf.comp φ hgraph
  have he : D.comp ((ContinuousLinearMap.id ℂ PotPair).prod L) =
      normingSpectral38 φ z • L + normingCLM38 φ z := by
    apply ContinuousLinearMap.ext
    intro v
    change D (v,L v) = normingSpectral38 φ z * L v + normingCLM38 φ z v
    have hp := congrArg (fun A : PotPair →L[ℂ] ℂ => A v)
      (norming_joint_potential_partial38 φ z)
    change D (v,0) = normingCLM38 φ z v at hp
    have hs : D (0,1) = normingSpectral38 φ z := norming_joint_spectral_partial38 φ z
    rw [complex_linear_split D,hp,hs]
    ring
  rw [he] at h
  exact h

theorem kappaCLM_at_dirichlet_root38 (φ : PotPair) (z : ℂ)
    (hr : dirichletChar φ z = 0) (hs : deriv (dirichletChar φ) z ≠ 0) :
    kappaCLM38 φ z = (2/normingFactor φ z) •
      (normingSpectral38 φ z • dirImplicitGradient φ z + normingCLM38 φ z) := by
  have _hU := normingFactor_ne_zero_at_dirichlet_root38 φ z hr
  have _hQ := dirichlet_Q_ne_zero φ z hr hs
  rw [kappaCLM38,kappaKernel38,integralPairCLM38_kernelSmul,
    integralPairCLM38_kernelAdd,integralPairCLM38_kernelSmul,
    ← dirImplicitGradient_eq_kernel38 φ z hr hs]
  rfl

end
end NlsGge.GK38.PoissonMixed38
