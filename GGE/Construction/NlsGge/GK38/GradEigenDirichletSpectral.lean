import NlsGge.GK38.GradEigenDirichletAlgebra

set_option autoImplicit false
open Set Filter Topology MeasureTheory
namespace NlsGge.GK38.GradEigen38
noncomputable section
def dirichlet_spectral_value (φ : PotPair) (z : ℂ) : ℂ :=
  (fundSpectralIntegral38 φ z t1 1 0 + fundSpectralIntegral38 φ z t1 1 1 -
    fundSpectralIntegral38 φ z t1 0 0 - fundSpectralIntegral38 φ z t1 0 1)/(2*Complex.I)

theorem hasDerivAt_dirichlet_spectral (φ : PotPair) (z : ℂ) :
    HasDerivAt (dirichletChar φ) (dirichlet_spectral_value φ z) z := by
  have hd := (((hasDerivAt_fundSpectralIntegral38 φ z t1 1 0).fun_add
    (hasDerivAt_fundSpectralIntegral38 φ z t1 1 1)).fun_sub
    (hasDerivAt_fundSpectralIntegral38 φ z t1 0 0)).fun_sub
    (hasDerivAt_fundSpectralIntegral38 φ z t1 0 1)
  change HasDerivAt (fun w => dirichletChar φ w) (dirichlet_spectral_value φ z) z
  simpa only [dirichlet_spectral_value,dirichletChar_eq,monodromyPair_eq_fundPair,t1]
    using hd.div_const (2*Complex.I)

theorem dirichlet_spectral_Q (φ : PotPair) (z : ℂ) (hroot : dirichletChar φ z = 0) :
    dirichlet_spectral_value φ z =
      (monodromyPair φ z 1 1 - monodromyPair φ z 0 1) *
        Q (state φ z (![1,1] : PairVec38))/2 := by
  let M := monodromyPair φ z
  let F : ℝ → PairMat38 := ext38 (fundContP φ z)
  let A : ℝ → PairMat38 := fun s => (F s).adjugate * spectralCoeff38 * F s
  let w := state φ z (![1,1] : PairVec38)
  have hA (i j : Fin 2) : IntervalIntegrable (fun s => A s i j) volume 0 1 :=
    intervalIntegrable_fundSpectralKer38 φ z t1 i j
  have hMA (i j : Fin 2) : IntervalIntegrable (fun s => (M * A s) i j) volume 0 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact ((hA 0 j).const_mul (M i 0)).add ((hA 1 j).const_mul (M i 1))
  have hentry (i j : Fin 2) : fundSpectralIntegral38 φ z t1 i j =
      ∫ s in (0 : ℝ)..1, (M * A s) i j := by
    have hM : fundPair φ z t1 = M := by
      simpa only [t1] using (monodromyPair_eq_fundPair φ z).symm
    calc
      fundSpectralIntegral38 φ z t1 i j =
          (M * Matrix.of (fun a b => ∫ s in (0 : ℝ)..1, A s a b)) i j :=
        congrArg (fun K : PairMat38 =>
          (K * Matrix.of (fun a b => ∫ s in (0 : ℝ)..1, A s a b)) i j) hM
      _ = _ := k1MatIntegralLeft38 M A 1 hA i j
  have hw (s : ℝ) (i : Fin 2) : pairKernelExt38 w s i = F s i 0 + F s i 1 := by
    rw [state_ext]
    simp [F]
  have hr := dirichlet_boundary_sum φ z hroot
  have _hQ := (kernel_integrability w).1
  have hInt : (∫ s in (0 : ℝ)..1,
      (M * A s) 1 0 + (M * A s) 1 1 - (M * A s) 0 0 - (M * A s) 0 1) =
      (2*Complex.I*(M 1 1-M 0 1)) *
        ∫ s in (0 : ℝ)..1, pairKernelExt38 w s 0 * pairKernelExt38 w s 1 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    change (M * A s) 1 0 + (M * A s) 1 1 - (M * A s) 0 0 - (M * A s) 0 1 =
      (2*Complex.I*(M 1 1-M 0 1)) * (pairKernelExt38 w s 0 * pairKernelExt38 w s 1)
    have hp := dirichlet_spectral_algebra M (F s) hr
    simpa only [A,hw,mul_assoc] using hp
  unfold dirichlet_spectral_value
  rw [hentry,hentry,hentry,hentry]
  rw [← intervalIntegral.integral_add (hMA 1 0) (hMA 1 1),
    ← intervalIntegral.integral_sub ((hMA 1 0).add (hMA 1 1)) (hMA 0 0),
    ← intervalIntegral.integral_sub (((hMA 1 0).add (hMA 1 1)).sub (hMA 0 0)) (hMA 0 1), hInt]
  change ((2*Complex.I*(M 1 1-M 0 1)) *
    ∫ s in (0 : ℝ)..1, pairKernelExt38 w s 0 * pairKernelExt38 w s 1)/(2*Complex.I) =
    (M 1 1-M 0 1)*(2*∫ s in (0 : ℝ)..1,
      pairKernelExt38 w s 0 * pairKernelExt38 w s 1)/2
  field_simp


end
end NlsGge.GK38.GradEigen38
