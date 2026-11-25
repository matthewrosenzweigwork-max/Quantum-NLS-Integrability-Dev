import NlsGge.GK38.GradEigenNorming

set_option autoImplicit false
open Set Filter Topology MeasureTheory
namespace NlsGge.GK38.GradEigen38
noncomputable section
theorem dirichlet_boundary_sum (φ : PotPair) (z : ℂ) (hroot : dirichletChar φ z = 0) :
    monodromyPair φ z 1 0 + monodromyPair φ z 1 1 -
      monodromyPair φ z 0 0 - monodromyPair φ z 0 1 = 0 := by
  rw [dirichletChar_eq] at hroot
  exact (div_eq_zero_iff).mp hroot |>.resolve_right dirichlet_denominator_ne_zero38

theorem dirichlet_amplitude_inverse (φ : PotPair) (z : ℂ)
    (hroot : dirichletChar φ z = 0) :
    (monodromyPair φ z 0 0 + monodromyPair φ z 0 1) *
      (monodromyPair φ z 1 1 - monodromyPair φ z 0 1) = 1 := by
  have hr := dirichlet_boundary_sum φ z hroot
  have hd := monodromy_det_scalar φ z
  linear_combination hd + monodromyPair φ z 0 1 * hr

theorem dirichlet_amplitudes_nonzero (φ : PotPair) (z : ℂ)
    (hroot : dirichletChar φ z = 0) :
    monodromyPair φ z 0 0 + monodromyPair φ z 0 1 ≠ 0 ∧
    monodromyPair φ z 1 1 - monodromyPair φ z 0 1 ≠ 0 := by
  apply mul_ne_zero_iff.mp
  rw [dirichlet_amplitude_inverse φ z hroot]
  exact one_ne_zero

theorem dirichlet_entry_kernel_at_root (φ : PotPair) (z : ℂ)
    (hroot : dirichletChar φ z = 0) :
    fundamentalEntryKernelCont38 φ z t1 1 0 + fundamentalEntryKernelCont38 φ z t1 1 1 -
      fundamentalEntryKernelCont38 φ z t1 0 0 - fundamentalEntryKernelCont38 φ z t1 0 1 =
      (-Complex.I * (monodromyPair φ z 1 1 - monodromyPair φ z 0 1)) •
        square (state φ z (![1,1] : PairVec38)) := by
  have hr := dirichlet_boundary_sum φ z hroot
  ext t i
  fin_cases i <;>
    simp [fundamentalEntryKernelCont38, fundamentalScaledKernel38,
      square, state, starProd38, ← monodromyPair_eq_fundPair, t1]
  · linear_combination (Complex.I * (fundColumn38 φ z t 0 1 + fundColumn38 φ z t 1 1) *
      fundColumn38 φ z t 1 1) * hr
  · linear_combination (Complex.I * (fundColumn38 φ z t 0 0 + fundColumn38 φ z t 1 0) *
      fundColumn38 φ z t 1 0) * hr

theorem dirichlet_spectral_algebra (M F : PairMat38)
    (hr : M 1 0 + M 1 1 - M 0 0 - M 0 1 = 0) :
    (M * (F.adjugate * spectralCoeff38 * F)) 1 0 +
      (M * (F.adjugate * spectralCoeff38 * F)) 1 1 -
      (M * (F.adjugate * spectralCoeff38 * F)) 0 0 -
      (M * (F.adjugate * spectralCoeff38 * F)) 0 1 =
      (2 * Complex.I) * (M 1 1 - M 0 1) * (F 0 0 + F 0 1) * (F 1 0 + F 1 1) := by
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.adjugate_fin_two,
    spectralCoeff38, Fin.sum_univ_two]
  linear_combination (-Complex.I * (F 0 0 * F 1 1 + F 0 1 * F 1 0 +
    2 * F 0 1 * F 1 1)) * hr


end
end NlsGge.GK38.GradEigen38
