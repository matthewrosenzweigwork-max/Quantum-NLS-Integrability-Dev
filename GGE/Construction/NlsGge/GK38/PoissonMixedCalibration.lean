import NlsGge.GK38.PoissonMixedNormingData

/-! Mandatory actual free norming derivative and both ordered bracket signs.
These concrete computations precede every general mixed bracket theorem. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem free_norming_kernel38 (t : Time) :
    normingKernel38 0 0 t = ![Complex.I/2,-Complex.I/2] := by
  have hm : monodromyPair 0 0 = (1 : PairMat38) := by
    rw [monodromyPair_zero_potential]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [freeE]
  have hk : terminalSeed 0 0 = (![1,-1] : PairVec38) := by
    ext i
    fin_cases i <;> norm_num [terminalSeed,hm]
  have hg : state 0 0 ![1,1] t = (![1,1] : PairVec38) := by
    rw [probe_free_state]
    norm_num
  have hkt : state 0 0 (terminalSeed 0 0) t = (![1,-1] : PairVec38) := by
    rw [hk,probe_free_state]
    norm_num
  ext i
  fin_cases i <;> norm_num [normingKernel38,mixedSquare,hg,hkt,starProd38] <;> ring

theorem free_kappa_kernel_eq38 :
    kappaKernel38 0 0 = (2 : ℂ) • normingKernel38 0 0 := by
  ext t i
  change (2 / normingFactor 0 0) *
    (normingSpectral38 0 0 * dirEigenKernel38 0 0 t i + normingKernel38 0 0 t i) =
      2 * normingKernel38 0 0 t i
  rw [normingFactor_free38,Complex.cos_zero,normingSpectral_free_zero38,
    zero_mul,zero_add,div_one]

theorem free_kappa_kernel38 (t : Time) : kappaKernel38 0 0 t = ![Complex.I,-Complex.I] := by
  rw [free_kappa_kernel_eq38]
  change (2 : ℂ) • (normingKernel38 0 0 t) = _
  rw [free_norming_kernel38]
  ext i
  fin_cases i <;> norm_num <;> ring

theorem free_mu_hamField38 :
    kernelHamField38 (dirEigenKernel38 0 0) = realSlice (constL2 (-Complex.I/2)) := by
  change dirEigenHamField38 0 0 = _
  exact probe_free_central_hamField38.2.2

theorem free_signed_norming38 : signedNorming38 0 0 = 1 := by
  simp only [signedNorming38,parity,zpow_zero,one_mul,realSlice_zero,gkMu_free38,
    Int.cast_zero,zero_mul,Complex.ofReal_zero,normingFactor_free38,Complex.cos_zero,
    Complex.one_re]

theorem hasFDerivAt_free_norming_label38 :
    HasFDerivAt (fun v : PhysicalL2 => normingFactor (realSlice v) (gkMu v 0 : ℂ))
      (((normingCLM38 0 0).restrictScalars ℝ).comp realSlice) 0 := by
  let f : PotPair × ℂ → ℂ := fun p => normingFactor p.1 p.2
  let D := fderiv ℂ f (0,0)
  let dr := fderiv ℝ (fun v : PhysicalL2 => gkMu v 0) 0
  have hf0 : HasFDerivAt f D (0,0) :=
    (analyticOnNhd_normingFactor38 (0,0) (mem_univ _)).differentiableAt.hasFDerivAt
  have hf : HasFDerivAt f D (realSlice 0,(gkMu 0 0 : ℂ)) := by
    simpa only [realSlice_zero,gkMu_free38,Int.cast_zero,zero_mul,Complex.ofReal_zero] using hf0
  have hr : HasFDerivAt (fun v : PhysicalL2 => gkMu v 0) dr 0 :=
    (analyticAt_gkMu38 0 0).differentiableAt.hasFDerivAt
  have hgraph : HasFDerivAt (fun v : PhysicalL2 => (realSlice v,(gkMu v 0 : ℂ)))
      (realSlice.prod (Complex.ofRealCLM.comp dr)) 0 :=
    realSlice.hasFDerivAt.prodMk (Complex.ofRealCLM.hasFDerivAt.comp 0 hr)
  have h := (hf.restrictScalars ℝ).comp 0 hgraph
  have he : (D.restrictScalars ℝ).comp (realSlice.prod (Complex.ofRealCLM.comp dr)) =
      ((normingCLM38 0 0).restrictScalars ℝ).comp realSlice := by
    apply ContinuousLinearMap.ext
    intro v
    change D (realSlice v,(dr v : ℂ)) = normingCLM38 0 0 (realSlice v)
    have hp := congrArg (fun L : PotPair →L[ℂ] ℂ => L (realSlice v))
      (norming_joint_potential_partial38 0 0)
    change D (realSlice v,0) = normingCLM38 0 0 (realSlice v) at hp
    have hs : D (0,1) = 0 := by
      change (fderiv ℂ (fun p : PotPair × ℂ => normingFactor p.1 p.2) (0,0)) (0,1) = 0
      rw [norming_joint_spectral_partial38,normingSpectral_free_zero38]
    rw [complex_linear_split D, hp,hs,mul_zero,add_zero]
  rw [he] at h
  exact h

theorem free_realKappaCLM38 :
    realKappaCLM38 0 0 = (2 : ℝ) •
      (Complex.reCLM.comp (((normingCLM38 0 0).restrictScalars ℝ).comp realSlice)) := by
  unfold realKappaCLM38
  simp only [realSlice_zero,gkMu_free38,Int.cast_zero,zero_mul,Complex.ofReal_zero]
  rw [kappaCLM38,free_kappa_kernel_eq38,integralPairCLM38_kernelSmul]
  apply ContinuousLinearMap.ext
  intro h
  change ((2 : ℂ) * normingCLM38 0 0 (realSlice h)).re =
    2 * (normingCLM38 0 0 (realSlice h)).re
  simp

theorem hasFDerivAt_free_realKappa38 :
    HasFDerivAt (fun v : PhysicalL2 => realKappa38 v 0) (realKappaCLM38 0 0) 0 := by
  have h := Complex.reCLM.hasFDerivAt.comp 0 hasFDerivAt_free_norming_label38
  have hs : HasFDerivAt (fun v : PhysicalL2 => signedNorming38 v 0)
      (Complex.reCLM.comp (((normingCLM38 0 0).restrictScalars ℝ).comp realSlice)) 0 := by
    convert! h using 1 <;> simp only [signedNorming38,parity,zpow_zero,one_mul,Function.comp_def] <;> rfl
  have hd := (hs.log (by rw [free_signed_norming38]; norm_num)).const_mul (2 : ℝ)
  rw [free_signed_norming38,inv_one,one_smul,← free_realKappaCLM38] at hd
  exact hd

theorem free_kappa_pairing38 :
    integralPairCLM38 (kappaKernel38 0 0) t1 (realSlice (constL2 (-Complex.I/2))) = 1 := by
  have _hi := intervalIntegrable_pairKernel38 (kappaKernel38 0 0) t1
    (realSlice (constL2 (-Complex.I/2)))
  have he (s : ℝ) : pairKernelExt38 (kappaKernel38 0 0) s = ![Complex.I,-Complex.I] :=
    free_kappa_kernel38 (projIcc 0 1 zero_le_one s)
  change pairIntegral38 (kappaKernel38 0 0) t1 (realSlice (constL2 (-Complex.I/2))) = 1
  rw [realSlice_constL2]
  unfold pairIntegral38
  have hae : (fun s => pairKernelExt38 (kappaKernel38 0 0) s 0 *
      potRepFst38 (constL2 (-Complex.I/2),constL2 (star (-Complex.I/2))) s +
      pairKernelExt38 (kappaKernel38 0 0) s 1 *
      potRepSnd38 (constL2 (-Complex.I/2),constL2 (star (-Complex.I/2))) s)
      =ᵐ[volume] fun _ => (1 : ℂ) := by
    filter_upwards [coverRep38_const_ae (-Complex.I/2),
      coverRep38_const_ae (star (-Complex.I/2))] with s h0 h1
    simp only [he,potRepFst38,potRepSnd38,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [h0,h1]
    norm_num [Complex.I_sq] <;> ring_nf <;> norm_num [Complex.I_sq]
  rw [intervalIntegral.integral_congr_ae (by filter_upwards [hae] with s hs _ using hs)]
  simp [t1]

theorem actual_free_realKappa_direction38 :
    (fderiv ℝ (fun v : PhysicalL2 => realKappa38 v 0) 0) (constL2 (-Complex.I/2)) = 1 := by
  rw [hasFDerivAt_free_realKappa38.fderiv]
  change (integralPairCLM38 (kappaKernel38 (realSlice 0) (gkMu 0 0 : ℂ)) t1
    (realSlice (constL2 (-Complex.I/2)))).re = 1
  simp only [realSlice_zero,gkMu_free38,Int.cast_zero,zero_mul,Complex.ofReal_zero]
  rw [free_kappa_pairing38]
  norm_num

theorem free_ordered_kappa_mu_brackets38 :
    kernelPoisson38 (kappaKernel38 0 0) (dirEigenKernel38 0 0) = 1 ∧
    kernelPoisson38 (dirEigenKernel38 0 0) (kappaKernel38 0 0) = -1 := by
  have he (s : ℝ) : pairKernelExt38 (kappaKernel38 0 0) s = ![Complex.I,-Complex.I] :=
    free_kappa_kernel38 (projIcc 0 1 zero_le_one s)
  have hmu (s : ℝ) : pairKernelExt38 (dirEigenKernel38 0 0) s = ![1/2,1/2] :=
    probe_free_central_hamField38.2.1 (projIcc 0 1 zero_le_one s)
  have _hi : IntervalIntegrable
      (kernelWedge38 (kappaKernel38 0 0) (dirEigenKernel38 0 0)) volume 0 1 :=
    (((continuous_component (kappaKernel38 0 0) 0).mul
    (continuous_component (dirEigenKernel38 0 0) 1)).sub
      ((continuous_component (kappaKernel38 0 0) 1).mul
        (continuous_component (dirEigenKernel38 0 0) 0))).intervalIntegrable 0 1
  have _hiRev : IntervalIntegrable
      (kernelWedge38 (dirEigenKernel38 0 0) (kappaKernel38 0 0)) volume 0 1 :=
    (((continuous_component (dirEigenKernel38 0 0) 0).mul
    (continuous_component (kappaKernel38 0 0) 1)).sub
      ((continuous_component (dirEigenKernel38 0 0) 1).mul
        (continuous_component (kappaKernel38 0 0) 0))).intervalIntegrable 0 1
  constructor <;> norm_num [kernelPoisson38,kernelWedge38,he,hmu,Complex.I_sq] <;>
    ring_nf <;> norm_num [Complex.I_sq]

theorem freeKappaCalibrationTarget : FreeKappaCalibrationTarget := by
  refine ⟨?_,?_,normingSpectral_free_zero38,fun t =>
    ⟨free_norming_kernel38 t,free_kappa_kernel38 t⟩,free_mu_hamField38,
    free_ordered_kappa_mu_brackets38.1,free_ordered_kappa_mu_brackets38.2,
    hasFDerivAt_free_realKappa38,actual_free_realKappa_direction38⟩
  · simp only [realKappa38,free_signed_norming38,Real.log_one,mul_zero]
  · rw [normingFactor_free38,Complex.cos_zero]

theorem free_calibration_direction_nonzero38 : constL2 (-Complex.I/2) ≠ 0 := by
  intro h
  have hd := actual_free_realKappa_direction38
  rw [h,map_zero] at hd
  exact zero_ne_one hd

end
end NlsGge.GK38.PoissonMixed38
