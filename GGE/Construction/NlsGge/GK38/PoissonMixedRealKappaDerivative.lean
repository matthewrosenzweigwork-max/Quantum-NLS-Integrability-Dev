import NlsGge.GK38.PoissonMixedRealKernel

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem hasFDerivAt_real_norming_graph38 (u : PhysicalL2) (n : ℤ) :
    HasFDerivAt (fun v : PhysicalL2 => normingFactor (realSlice v) (gkMu v n : ℂ))
      (((normingSpectral38 (realSlice u) (gkMu u n : ℂ) •
        dirImplicitGradient (realSlice u) (gkMu u n : ℂ) +
        normingCLM38 (realSlice u) (gkMu u n : ℂ)).restrictScalars ℝ).comp realSlice) u := by
  let f : PotPair × ℂ → ℂ := fun p => normingFactor p.1 p.2
  let D := fderiv ℂ f (realSlice u,(gkMu u n : ℂ))
  let dr := fderiv ℝ (fun v : PhysicalL2 => gkMu v n) u
  have hf : HasFDerivAt f D (realSlice u,(gkMu u n : ℂ)) :=
    (analyticOnNhd_normingFactor38 _ (mem_univ _)).differentiableAt.hasFDerivAt
  have hr : HasFDerivAt (fun v : PhysicalL2 => gkMu v n) dr u :=
    (analyticAt_gkMu38 u n).differentiableAt.hasFDerivAt
  have hg := realSlice.hasFDerivAt.prodMk (Complex.ofRealCLM.hasFDerivAt.comp u hr)
  have h := (hf.restrictScalars ℝ).comp u hg
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro v
  change normingSpectral38 (realSlice u) (gkMu u n : ℂ) *
      dirImplicitGradient (realSlice u) (gkMu u n : ℂ) (realSlice v) +
      normingCLM38 (realSlice u) (gkMu u n : ℂ) (realSlice v) = D (realSlice v,(dr v : ℂ))
  have hp := congrArg (fun L : PotPair →L[ℂ] ℂ => L (realSlice v))
    (norming_joint_potential_partial38 (realSlice u) (gkMu u n : ℂ))
  change D (realSlice v,0) = normingCLM38 (realSlice u) (gkMu u n : ℂ) (realSlice v) at hp
  have hs : D (0,1) = normingSpectral38 (realSlice u) (gkMu u n : ℂ) :=
    norming_joint_spectral_partial38 (realSlice u) (gkMu u n : ℂ)
  have hd := actual_dirichlet_label_complex_gradient u n v
  change (dr v : ℂ) = dirImplicitGradient (realSlice u) (gkMu u n : ℂ) (realSlice v) at hd
  rw [complex_linear_split D,hp,hs,hd]
  ring

theorem signedNorming_ofReal38 (u : PhysicalL2) (n : ℤ) :
    (signedNorming38 u n : ℂ) = parity n * normingFactor (realSlice u) (gkMu u n : ℂ) := by
  have hp : (parity n).im=0 := by
    have h := congrArg Complex.im (parity_star n)
    change -(parity n).im=(parity n).im at h
    linarith
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im,Complex.mul_im,hp,normingFactor_real_im38,
      zero_mul,mul_zero,add_zero]

theorem hasFDerivAt_realKappa38 (u : PhysicalL2) (n : ℤ) :
    HasFDerivAt (fun v : PhysicalL2 => realKappa38 v n) (realKappaCLM38 u n) u := by
  let B : PotPair →L[ℂ] ℂ := normingSpectral38 (realSlice u) (gkMu u n : ℂ) •
    dirImplicitGradient (realSlice u) (gkMu u n : ℂ) +
      normingCLM38 (realSlice u) (gkMu u n : ℂ)
  let R := (B.restrictScalars ℝ).comp realSlice
  let S := Complex.reCLM.comp (parity n • R)
  have hS : HasFDerivAt (fun v : PhysicalL2 => signedNorming38 v n) S u := by
    convert! Complex.reCLM.hasFDerivAt.comp u
      ((hasFDerivAt_real_norming_graph38 u n).const_mul (parity n)) using 1
  have hpositive := signedNorming_positive38 u n
  have hlog := (hS.log (ne_of_gt hpositive)).const_mul (2 : ℝ)
  have hU := normingFactor_ne_zero_at_dirichlet_root38 _ _ (gkMu_root38 u n)
  have hsimple := dirichlet_root_deriv_ne_zero38 u (gkMu u n) (gkMu_root38 u n)
  have hp : parity n ≠ 0 := by
    intro hz
    have h := parity_square n
    rw [hz,zero_pow (by decide : 2 ≠ 0)] at h
    norm_num at h
  have hc : (((2 : ℝ)/signedNorming38 u n : ℝ) : ℂ)*parity n =
      2/normingFactor (realSlice u) (gkMu u n : ℂ) := by
    push_cast
    rw [signedNorming_ofReal38]
    field_simp
  have he : (2 : ℝ) • ((signedNorming38 u n)⁻¹ • S) = realKappaCLM38 u n := by
    apply ContinuousLinearMap.ext
    intro v
    rw [realKappaCLM38,kappaCLM_at_dirichlet_root38 _ _ (gkMu_root38 u n) hsimple]
    change 2*((signedNorming38 u n)⁻¹*(parity n * R v).re) =
      ((2/normingFactor (realSlice u) (gkMu u n : ℂ))*R v).re
    rw [← hc]
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,mul_zero,sub_zero,add_zero,div_eq_mul_inv]
    ring
  rw [he] at hlog
  exact hlog

end
end NlsGge.GK38.PoissonMixed38
