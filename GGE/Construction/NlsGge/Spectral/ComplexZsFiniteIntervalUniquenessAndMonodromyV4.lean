import NlsGge.Spectral.ComplexZsGlobalSolutionOnIccAfterFiniteGluingV6
import NlsGge.Spectral.ComplexZsSourcePiNormLipschitzAfterNNRealPrerequisiteV2
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Order.LeftRightNhds

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

local instance uniquenessMatrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) :=
  instAnyInitialSourcePiNormedAddCommGroup

local instance uniquenessMatrixNormedSpace :
    NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  instAnyInitialSourcePiNormedSpace

set_option backward.isDefEq.respectTransparency false in
theorem eqOn_of_same_initial_actual_complexZs_solutions_Icc
    (u : ℝ → ℂ) (z : ℂ)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2))
    (F G : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hF0 : F 0 = 1) (hG0 : G 0 = 1)
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      HasDerivWithinAt F (zsCoefficientComplex u z t * F t)
        (Set.Icc (0 : ℝ) 2) t)
    (hG : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      HasDerivWithinAt G (zsCoefficientComplex u z t * G t)
        (Set.Icc (0 : ℝ) 2) t) :
    Set.EqOn F G (Set.Icc (0 : ℝ) 2) := by
  obtain ⟨K, hK⟩ := exists_uniform_complexZsVectorField_lipschitzOn_sourcePiNorm_Icc u z hu
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 2) := by
    intro t ht
    exact (hF t ht).continuousWithinAt
  have hGcont : ContinuousOn G (Set.Icc (0 : ℝ) 2) := by
    intro t ht
    exact (hG t ht).continuousWithinAt
  have hFici : ∀ t ∈ Set.Ico (0 : ℝ) 2,
      HasDerivWithinAt F (zsCoefficientComplex u z t * F t) (Set.Ici t) t := by
    intro t ht
    exact (hF t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2⟩)
  have hGici : ∀ t ∈ Set.Ico (0 : ℝ) 2,
      HasDerivWithinAt G (zsCoefficientComplex u z t * G t) (Set.Ici t) t := by
    intro t ht
    exact (hG t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2⟩)
  have hinitial : F 0 = G 0 := hF0.trans hG0.symm
  exact ODE_solution_unique_of_mem_Icc_right
    (fun t ht => (hK t ⟨ht.1, ht.2.le⟩).lipschitzOnWith)
    hFcont hFici (fun _ _ => Set.mem_univ _)
    hGcont hGici (fun _ _ => Set.mem_univ _) hinitial

theorem exists_normalized_actual_complexZs_solution_Icc
    (u : ℝ → ℂ) (z : ℂ)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2)) :
    ∃ F : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      F 0 = 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 2,
        HasDerivWithinAt F (zsCoefficientComplex u z t * F t)
          (Set.Icc (0 : ℝ) 2) t :=
  exists_global_complexZs_matrix_solution_on_Icc_V1 u z hu 1

theorem normalized_actual_complexZs_monodromy_and_trace_independent_Icc
    (u : ℝ → ℂ) (z : ℂ)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2))
    (F G : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hF0 : F 0 = 1) (hG0 : G 0 = 1)
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      HasDerivWithinAt F (zsCoefficientComplex u z t * F t)
        (Set.Icc (0 : ℝ) 2) t)
    (hG : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      HasDerivWithinAt G (zsCoefficientComplex u z t * G t)
        (Set.Icc (0 : ℝ) 2) t)
    (period : ℝ) (hperiod : period ∈ Set.Icc (0 : ℝ) 2) :
    zsMonodromy F period = zsMonodromy G period ∧
      zsFullTrace F period = zsFullTrace G period := by
  have hEq := eqOn_of_same_initial_actual_complexZs_solutions_Icc
    u z hu F G hF0 hG0 hF hG
  have hperiodEq : F period = G period := hEq hperiod
  constructor
  · simpa [zsMonodromy] using hperiodEq
  · simp [zsFullTrace, zsMonodromy, hperiodEq]

end NlsGge.SpectralFoundations

end
