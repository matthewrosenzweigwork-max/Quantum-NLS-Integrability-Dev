import NlsGge.GK38.PoissonMixedDiscriminantIntegral

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem discrim_dir_wedge_eq_columns38 (φ : PotPair) (z ζ : ℂ)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    kernelWedge38 (gradDiscrimCont38 φ ζ) (dirEigenKernel38 φ z) r =
      (-Complex.I)*(Q (state φ z ![1,1]))⁻¹ *
      (monodromyPair φ ζ 0 1*columnDirWedge38 φ z ζ 0 0 r +
        (monodromyPair φ ζ 1 1-monodromyPair φ ζ 0 0)*columnDirWedge38 φ z ζ 0 1 r -
        monodromyPair φ ζ 1 0*columnDirWedge38 φ z ζ 1 1 r) := by
  have hg : pairKernelExt38 (gradDiscrimCont38 φ ζ) r = gradDiscrim38 φ ζ r := by
    rw [pairKernelExt38_of_mem _ hr]
    rfl
  unfold kernelWedge38
  rw [hg]
  simp only [gradDiscrim38,dirEigenKernel38,pairKernelExt38,
    Set.IccExtend,Function.comp_apply,ContinuousMap.smul_apply,Pi.smul_apply,
    Pi.add_apply,Pi.sub_apply,smul_eq_mul,square,ContinuousMap.coe_mk,
    columnDirWedge38,pairBracket38,starProd38,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

theorem discrim_dir_poisson_eq_weightedIntegral38 (φ : PotPair) (z ζ : ℂ) :
    kernelPoisson38 (gradDiscrimCont38 φ ζ) (dirEigenKernel38 φ z) =
      -(Q (state φ z ![1,1]))⁻¹ * weightedColumnDirIntegral38 φ z ζ := by
  have _hw := intervalIntegrable_kernelWedge38 (gradDiscrimCont38 φ ζ) (dirEigenKernel38 φ z)
  have h00 := intervalIntegrable_columnDirWedge38 φ z ζ 0 0
  have h01 := intervalIntegrable_columnDirWedge38 φ z ζ 0 1
  have h11 := intervalIntegrable_columnDirWedge38 φ z ζ 1 1
  have he : (∫ r in (0 : ℝ)..1,
      kernelWedge38 (gradDiscrimCont38 φ ζ) (dirEigenKernel38 φ z) r) =
      (-Complex.I)*(Q (state φ z ![1,1]))⁻¹ * weightedColumnDirIntegral38 φ z ζ := by
    calc
      (∫ r in (0 : ℝ)..1,
        kernelWedge38 (gradDiscrimCont38 φ ζ) (dirEigenKernel38 φ z) r) =
        ∫ r in (0 : ℝ)..1, (-Complex.I)*(Q (state φ z ![1,1]))⁻¹ *
          (monodromyPair φ ζ 0 1*columnDirWedge38 φ z ζ 0 0 r +
            (monodromyPair φ ζ 1 1-monodromyPair φ ζ 0 0)*columnDirWedge38 φ z ζ 0 1 r -
            monodromyPair φ ζ 1 0*columnDirWedge38 φ z ζ 1 1 r) := by
        apply intervalIntegral.integral_congr
        intro r hr
        exact discrim_dir_wedge_eq_columns38 φ z ζ r (by simpa only [uIcc_of_le zero_le_one] using hr)
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub
            ((h00.const_mul _).add (h01.const_mul _)) (h11.const_mul _),
          intervalIntegral.integral_add (h00.const_mul _) (h01.const_mul _),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
        rfl
  unfold kernelPoisson38
  rw [he]
  ring_nf
  simp [Complex.I_sq]

end
end NlsGge.GK38.PoissonMixed38
