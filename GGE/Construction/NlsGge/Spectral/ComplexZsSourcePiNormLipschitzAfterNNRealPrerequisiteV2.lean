import NlsGge.Spectral.FreeZakharovShabatFundamentalComplexV4
import NlsGge.Spectral.ComplexScalarCompactNormBoundPrerequisiteV3
import NlsGge.Spectral.ComplexZsSourcePiNNRealCoefficientV2
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Matrix.Normed

/-!
Source-dictionary route for the ZS Picard theorem: coefficient bounds and
state-Lipschitz estimates in the actual matrix Pi norm, without transporting
derivatives between the source Pi topology and the separate Frobenius norm.
-/

set_option autoImplicit false

open scoped NNReal

noncomputable section

namespace NlsGge.SpectralFoundations

local instance instSourcePiNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedAddCommGroup

local instance instSourcePiNormedSpace :
    NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedSpace

theorem norm_mul_matrix_fin2_le (A X : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖A * X‖ ≤ 2 * ‖A‖ * ‖X‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  calc
    ‖A i 0 * X 0 j + A i 1 * X 1 j‖ ≤
        ‖A i 0 * X 0 j‖ + ‖A i 1 * X 1 j‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖X‖ + ‖A‖ * ‖X‖ := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul
          ((norm_le_pi_norm (A i) 0).trans (norm_le_pi_norm A i))
          ((norm_le_pi_norm (X 0) j).trans (norm_le_pi_norm X 0))
          (norm_nonneg _) (norm_nonneg _)
      · rw [norm_mul]
        exact mul_le_mul
          ((norm_le_pi_norm (A i) 1).trans (norm_le_pi_norm A i))
          ((norm_le_pi_norm (X 1) j).trans (norm_le_pi_norm X 1))
          (norm_nonneg _) (norm_nonneg _)
    _ = 2 * ‖A‖ * ‖X‖ := by ring

theorem exists_bound_zsCoefficientComplex_sourcePiNorm
    (u : ℝ → ℂ) (z : ℂ)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 2,
      ‖zsCoefficientComplex u z t‖ ≤ C := by
  obtain ⟨Cu, hCu⟩ := exists_bound_complex_norm_of_continuousOn u hu
  let C : ℝ := max ‖z‖ Cu
  have hC : 0 ≤ C := le_max_of_le_left (norm_nonneg _)
  have hentry (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2)
      (i j : Fin 2) :
      ‖zsCoefficientComplex u z t i j‖ ≤ C := by
    fin_cases i <;> fin_cases j <;>
      simp [C, zsCoefficientComplex, hCu t ht, norm_nonneg]
  refine ⟨C, hC, ?_⟩
  intro t ht
  change ‖fun i : Fin 2 => fun j : Fin 2 => zsCoefficientComplex u z t i j‖ ≤ C
  exact (pi_norm_le_iff_of_nonneg hC).2 fun i =>
    (pi_norm_le_iff_of_nonneg hC).2 fun j => hentry t ht i j

theorem exists_uniform_complexZsVectorField_lipschitzOn_sourcePiNorm_Icc
    (u : ℝ → ℂ) (z : ℂ)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2)) :
    ∃ K : ℝ≥0, ∀ t ∈ Set.Icc (0 : ℝ) 2,
      LipschitzWith K
        (fun X : Matrix (Fin 2) (Fin 2) ℂ => zsCoefficientComplex u z t * X) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_zsCoefficientComplex_sourcePiNorm u z hu
  let K : ℝ≥0 := ⟨2 * C, mul_nonneg (by norm_num) hC0⟩
  refine ⟨K, ?_⟩
  intro t ht
  apply LipschitzWith.of_dist_le_mul
  intro X Y
  simp only [dist_eq_norm]
  calc
    ‖zsCoefficientComplex u z t * X - zsCoefficientComplex u z t * Y‖ =
        ‖zsCoefficientComplex u z t * (X - Y)‖ := by rw [← Matrix.mul_sub]
    _ ≤ 2 * ‖zsCoefficientComplex u z t‖ * ‖X - Y‖ :=
      norm_mul_matrix_fin2_le _ _
    _ ≤ 2 * C * ‖X - Y‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hC t ht) (by norm_num)) (norm_nonneg _)
    _ = (K : ℝ) * ‖X - Y‖ := by
      rw [show (K : ℝ) = 2 * C from
        sourcePi_nnreal_lipschitzConstant_coe C hC0]

end NlsGge.SpectralFoundations
