import NlsGge.GK38.GradEigenPeriodicAlgebra
set_option autoImplicit false
open Set Filter Topology MeasureTheory
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem periodic_discrim_deriv_trace_integral (φ : PotPair) (z : ℂ) :
    deriv (discrim φ) z = ∫ s in (0 : ℝ)..1,
      (monodromyPair φ z * ((ext38 (fundContP φ z) s).adjugate * spectralCoeff38 *
        ext38 (fundContP φ z) s)) 0 0 +
      (monodromyPair φ z * ((ext38 (fundContP φ z) s).adjugate * spectralCoeff38 *
        ext38 (fundContP φ z) s)) 1 1 := by
  let M := monodromyPair φ z
  let A : ℝ → PairMat38 := fun s => (ext38 (fundContP φ z) s).adjugate *
    spectralCoeff38 * ext38 (fundContP φ z) s
  have hA (i j : Fin 2) : IntervalIntegrable (fun s => A s i j) volume 0 1 :=
    intervalIntegrable_fundSpectralKer38 φ z t1 i j
  have hMA (i j : Fin 2) : IntervalIntegrable (fun s => (M * A s) i j) volume 0 1 := by
    simp only [Matrix.mul_apply,Fin.sum_univ_two]
    exact ((hA 0 j).const_mul (M i 0)).add ((hA 1 j).const_mul (M i 1))
  have hentry (i j : Fin 2) : fundSpectralIntegral38 φ z t1 i j =
      ∫ s in (0 : ℝ)..1, (M * A s) i j := by
    have hM : fundPair φ z t1 = M := by
      simpa only [t1] using (monodromyPair_eq_fundPair φ z).symm
    calc
      fundSpectralIntegral38 φ z t1 i j =
          (M * Matrix.of (fun a b => ∫ s in (0 : ℝ)..1,A s a b)) i j :=
        congrArg (fun K : PairMat38 =>
          (K * Matrix.of (fun a b => ∫ s in (0 : ℝ)..1,A s a b)) i j) hM
      _ = _ := k1MatIntegralLeft38 M A 1 hA i j
  rw [deriv_discrim_spectral38]
  change fundSpectralIntegral38 φ z t1 0 0 + fundSpectralIntegral38 φ z t1 1 1 = _
  rw [hentry,hentry,← intervalIntegral.integral_add (hMA 0 0) (hMA 1 1)]

theorem periodic_scalar_spectral_deriv_zero (φ : PotPair) (z c : ℂ)
    (hscalar : monodromyPair φ z = c • (1 : PairMat38)) : deriv (discrim φ) z = 0 := by
  rw [periodic_discrim_deriv_trace_integral]
  have he (s : ℝ) :
      (monodromyPair φ z * ((ext38 (fundContP φ z) s).adjugate * spectralCoeff38 *
        ext38 (fundContP φ z) s)) 0 0 +
      (monodromyPair φ z * ((ext38 (fundContP φ z) s).adjugate * spectralCoeff38 *
        ext38 (fundContP φ z) s)) 1 1 = 0 := by
    rw [hscalar]
    exact periodic_spectral_scalar_algebra _ c
  simp only [he,intervalIntegral.integral_zero]

theorem periodic_spectral_Q01 (φ : PotPair) (z c : ℂ)
    (hs : c+c = monodromyPair φ z 0 0+monodromyPair φ z 1 1)
    (hc : c*c=1) (hb : monodromyPair φ z 0 1 ≠ 0) :
    deriv (discrim φ) z = (Complex.I*monodromyPair φ z 0 1) *
      Q (state φ z (floquetSeed01 φ z c)) := by
  let M := monodromyPair φ z
  let F : ℝ → PairMat38 := ext38 (fundContP φ z)
  let r := (c-M 0 0)/M 0 1
  let w := state φ z (floquetSeed01 φ z c)
  have hcoeff := floquet_coefficients _ _ _ _ _ _ hs hc (monodromy_det_scalar φ z) hb
  have hsum : 2*M 0 1*r=M 1 1-M 0 0 := by linear_combination hcoeff.1
  have hprod : M 0 1*r*r= -M 1 0 := hcoeff.2
  have hw (s : ℝ) (i : Fin 2) : pairKernelExt38 w s i = F s i 0+r*F s i 1 := by
    rw [state_ext]
    simp [w,floquetSeed01,F,r,M]
  have _hQ := (kernel_integrability w).1
  have he : (∫ s in (0 : ℝ)..1,
      (M*((F s).adjugate*spectralCoeff38*F s)) 0 0 +
      (M*((F s).adjugate*spectralCoeff38*F s)) 1 1) =
      (2*Complex.I*M 0 1) * ∫ s in (0 : ℝ)..1,
        pairKernelExt38 w s 0*pairKernelExt38 w s 1 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    have hp := periodic_spectral_chart01_algebra M (F s) r hsum hprod
    simpa only [hw,mul_assoc] using hp
  rw [periodic_discrim_deriv_trace_integral]
  change (∫ s in (0 : ℝ)..1,
      (M*((F s).adjugate*spectralCoeff38*F s)) 0 0 +
      (M*((F s).adjugate*spectralCoeff38*F s)) 1 1) = _
  rw [he]
  change (2*Complex.I*M 0 1)*(∫ s in (0 : ℝ)..1,
      pairKernelExt38 w s 0*pairKernelExt38 w s 1) =
    (Complex.I*M 0 1)*(2*∫ s in (0 : ℝ)..1,
      pairKernelExt38 w s 0*pairKernelExt38 w s 1)
  ring

theorem periodic_spectral_Q10 (φ : PotPair) (z c : ℂ)
    (hs : c+c = monodromyPair φ z 0 0+monodromyPair φ z 1 1)
    (hc : c*c=1) (hb : monodromyPair φ z 1 0 ≠ 0) :
    deriv (discrim φ) z = (-Complex.I*monodromyPair φ z 1 0) *
      Q (state φ z (floquetSeed10 φ z c)) := by
  let M := monodromyPair φ z
  let F : ℝ → PairMat38 := ext38 (fundContP φ z)
  let r := (c-M 1 1)/M 1 0
  let w := state φ z (floquetSeed10 φ z c)
  have hs' : c+c=M 1 1+M 0 0 := by
    calc
      c+c=M 0 0+M 1 1 := hs
      _ = M 1 1+M 0 0 := add_comm _ _
  have hd' : M 1 1*M 0 0-M 1 0*M 0 1=1 := by
    linear_combination monodromy_det_scalar φ z
  have hcoeff := floquet_coefficients _ _ _ _ _ _ hs' hc hd' hb
  have hsum : 2*M 1 0*r=M 0 0-M 1 1 := by linear_combination hcoeff.1
  have hprod : M 1 0*r*r= -M 0 1 := hcoeff.2
  have hw (s : ℝ) (i : Fin 2) : pairKernelExt38 w s i = r*F s i 0+F s i 1 := by
    rw [state_ext]
    simp [w,floquetSeed10,F,r,M]
  have _hQ := (kernel_integrability w).1
  have he : (∫ s in (0 : ℝ)..1,
      (M*((F s).adjugate*spectralCoeff38*F s)) 0 0 +
      (M*((F s).adjugate*spectralCoeff38*F s)) 1 1) =
      (-2*Complex.I*M 1 0) * ∫ s in (0 : ℝ)..1,
        pairKernelExt38 w s 0*pairKernelExt38 w s 1 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    have hp := periodic_spectral_chart10_algebra M (F s) r hsum hprod
    simpa only [hw,mul_assoc] using hp
  rw [periodic_discrim_deriv_trace_integral]
  change (∫ s in (0 : ℝ)..1,
      (M*((F s).adjugate*spectralCoeff38*F s)) 0 0 +
      (M*((F s).adjugate*spectralCoeff38*F s)) 1 1) = _
  rw [he]
  change (-2*Complex.I*M 1 0)*(∫ s in (0 : ℝ)..1,
      pairKernelExt38 w s 0*pairKernelExt38 w s 1) =
    (-Complex.I*M 1 0)*(2*∫ s in (0 : ℝ)..1,
      pairKernelExt38 w s 0*pairKernelExt38 w s 1)
  ring

end
end NlsGge.GK38.GradEigen38
