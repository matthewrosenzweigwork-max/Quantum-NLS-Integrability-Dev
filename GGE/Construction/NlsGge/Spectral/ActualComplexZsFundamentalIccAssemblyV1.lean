import NlsGge.Spectral.ComplexZsFiniteIntervalUniquenessAndMonodromyV4
import NlsGge.Spectral.ComplexZsLiouvilleDeterminantOneV2

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

local instance assemblyMatrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) :=
  instAnyInitialSourcePiNormedAddCommGroup

local instance assemblyMatrixNormedSpace :
    NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  instAnyInitialSourcePiNormedSpace

/-- The actual normalized complex-parameter ZS solution exists on `[0,2]`,
has determinant one there, and its values on the interval are independent of
the chosen total extension. -/
theorem exists_actual_normalized_complexZs_fundamental_Icc_det_unique
    (u : ℝ → ℂ) (z : ℂ)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2)) :
    ∃ F : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      F 0 = 1 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2,
        HasDerivWithinAt F (zsCoefficientComplex u z t * F t)
          (Set.Icc (0 : ℝ) 2) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2, Matrix.det (F t) = 1) ∧
      ∀ G : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
        G 0 = 1 →
        (∀ t ∈ Set.Icc (0 : ℝ) 2,
          HasDerivWithinAt G (zsCoefficientComplex u z t * G t)
            (Set.Icc (0 : ℝ) 2) t) →
        Set.EqOn F G (Set.Icc (0 : ℝ) 2) := by
  obtain ⟨F, hF0, hF⟩ :=
    exists_normalized_actual_complexZs_solution_Icc u z hu
  refine ⟨F, hF0, hF, ?_, ?_⟩
  · exact determinant_eq_one_of_normalized_actual_complexZs_solution_Icc
      u z F hF0 hF
  · intro G hG0 hG
    exact eqOn_of_same_initial_actual_complexZs_solutions_Icc
      u z hu F G hF0 hG0 hF hG

end NlsGge.SpectralFoundations

end
