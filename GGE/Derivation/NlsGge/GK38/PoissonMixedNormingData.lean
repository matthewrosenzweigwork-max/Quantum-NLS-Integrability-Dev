import NlsGge.GK38.PoissonMixedTargets

/-! Actual norming derivative data, before the mandatory free canonical calibration. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem analyticOnNhd_normingFactor38 :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => normingFactor p.1 p.2) univ := by
  have h := (((analyticOnNhd_monodromyPair 0 0).add
    (analyticOnNhd_monodromyPair 0 1)).add (analyticOnNhd_monodromyPair 1 0)).add
      (analyticOnNhd_monodromyPair 1 1)
  convert! h.div_const (c := (2 : ℂ)) using 1

theorem hasDerivAt_normingSpectral38 (φ : PotPair) (z : ℂ) :
    HasDerivAt (normingFactor φ) (normingSpectral38 φ z) z := by
  have hd := (((hasDerivAt_fundSpectralIntegral38 φ z t1 0 0).fun_add
    (hasDerivAt_fundSpectralIntegral38 φ z t1 0 1)).fun_add
    (hasDerivAt_fundSpectralIntegral38 φ z t1 1 0)).fun_add
    (hasDerivAt_fundSpectralIntegral38 φ z t1 1 1)
  convert! hd.div_const (2 : ℂ) using 1

theorem hasFDerivAt_normingCLM38 (φ : PotPair) (z : ℂ) :
    HasFDerivAt (fun ψ : PotPair => normingFactor ψ z) (normingCLM38 φ z) φ := by
  simpa only [normingCLM38,normingKernel38,integralPairCLM38_kernelSmul] using
    norming_derivative φ z

theorem normingDifferentiabilityTarget : NormingDifferentiabilityTarget :=
  ⟨analyticOnNhd_normingFactor38,fun φ z =>
    ⟨hasDerivAt_normingSpectral38 φ z,hasFDerivAt_normingCLM38 φ z⟩⟩

theorem norming_joint_potential_partial38 (φ : PotPair) (z : ℂ) :
    (fderiv ℂ (fun p : PotPair × ℂ => normingFactor p.1 p.2) (φ,z)).comp
      potentialInclusion = normingCLM38 φ z := by
  let f : PotPair × ℂ → ℂ := fun p => normingFactor p.1 p.2
  have hf : HasFDerivAt f (fderiv ℂ f (φ,z)) (φ,z) :=
    (analyticOnNhd_normingFactor38 (φ,z) (mem_univ _)).differentiableAt.hasFDerivAt
  have hcurve : HasFDerivAt (fun ψ : PotPair => (ψ,z)) potentialInclusion φ := by
    change HasFDerivAt (fun ψ : PotPair => (ψ,z)) (ContinuousLinearMap.inl ℂ PotPair ℂ) φ
    exact hasFDerivAt_prodMk_left (𝕜 := ℂ) φ z
  have hp := hf.comp φ hcurve
  change HasFDerivAt (fun ψ : PotPair => normingFactor ψ z)
    ((fderiv ℂ f (φ,z)).comp potentialInclusion) φ at hp
  exact hp.unique (hasFDerivAt_normingCLM38 φ z)

theorem norming_joint_spectral_partial38 (φ : PotPair) (z : ℂ) :
    (fderiv ℂ (fun p : PotPair × ℂ => normingFactor p.1 p.2) (φ,z)) (0,1) =
      normingSpectral38 φ z := by
  have hf := (analyticOnNhd_normingFactor38 (φ,z) (mem_univ _)).differentiableAt.hasFDerivAt
  have hcurve : HasDerivAt (fun w : ℂ => (φ,w)) ((0 : PotPair),(1 : ℂ)) z :=
    (hasDerivAt_const z φ).prodMk (hasDerivAt_id z)
  have hs : HasDerivAt (normingFactor φ)
      ((fderiv ℂ (fun p : PotPair × ℂ => normingFactor p.1 p.2) (φ,z)) (0,1)) z :=
    hf.comp_hasDerivAt z hcurve
  exact hs.unique (hasDerivAt_normingSpectral38 φ z)

theorem normingFactor_free38 (z : ℂ) : normingFactor 0 z = Complex.cos z := by
  rw [normingFactor,monodromyPair_zero_potential]
  simp only [freeE,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Complex.ofReal_one,mul_one,add_zero]
  rw [Complex.cos]
  congr 1
  rw [add_comm]
  congr 1 <;> congr 1 <;> ring

theorem normingSpectral_free_zero38 : normingSpectral38 0 0 = 0 := by
  have hd : HasDerivAt (normingFactor 0) 0 0 := by
    have he : normingFactor 0 = Complex.cos := funext normingFactor_free38
    rw [he]
    simpa only [Complex.sin_zero,neg_zero] using Complex.hasDerivAt_cos (0 : ℂ)
  exact (hasDerivAt_normingSpectral38 0 0).unique hd

end
end NlsGge.GK38.PoissonMixed38
