import NlsGge.Spectral.ComplexZsPicardCoefficientNormCastPrerequisiteV1
import NlsGge.Spectral.ComplexZsSourcePiNormLipschitzAfterNNRealPrerequisiteV2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.ODE.ExistUnique
import NlsGge.Spectral.ComplexZsUniformPicardStepScalarPrerequisiteV2

/-!
A uniform short-step existence lemma for the actual complex-parameter ZS
matrix equation, with arbitrary initial time/state inside `[0,2]`.  The
coefficient bound is an explicit helper input, derivable from the source
continuity assumption.  This is the local step for a later finite patch;
it does not claim global existence.
-/

open scoped NNReal

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

local instance instAnyInitialSourcePiNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedAddCommGroup

local instance instAnyInitialSourcePiNormedSpace :
    NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedSpace

theorem continuousOn_zsCoefficientComplex_any_initial_interval_V4
    (u : ℝ → ℂ) (z : ℂ) (a δ : ℝ)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (haδ : a + δ ≤ 2)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2)) :
    ContinuousOn (fun t : ℝ => zsCoefficientComplex u z t)
      (Set.Icc a (a + δ)) := by
  have huδ : ContinuousOn u (Set.Icc a (a + δ)) :=
    hu.mono (fun t ht => ⟨le_trans ha ht.1, ht.2.trans haδ⟩)
  apply continuousOn_pi.2
  intro i
  apply continuousOn_pi.2
  intro j
  fin_cases i <;> fin_cases j
  · simpa [zsCoefficientComplex] using
      (continuousOn_const : ContinuousOn
        (fun _ : ℝ => (-Complex.I * z)) (Set.Icc a (a + δ)))
  · refine ContinuousOn.congr
      ((continuousOn_const : ContinuousOn
        (fun _ : ℝ => Complex.I) (Set.Icc a (a + δ))).mul huδ) ?_
    intro t ht
    simp [zsCoefficientComplex, Pi.mul_apply]
  · refine ContinuousOn.congr
      ((continuousOn_const : ContinuousOn
        (fun _ : ℝ => -Complex.I) (Set.Icc a (a + δ))).mul huδ.star) ?_
    intro t ht
    simp [zsCoefficientComplex, Pi.mul_apply, neg_mul]
  · simpa [zsCoefficientComplex] using
      (continuousOn_const : ContinuousOn
        (fun _ : ℝ => Complex.I * z) (Set.Icc a (a + δ)) )

theorem exists_local_complexZs_matrix_solution_from_any_sourcePi_initial_state_V4
    (u : ℝ → ℂ) (z : ℂ)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2))
    (C : ℝ) (hC : 0 ≤ C)
    (hCoeff : ∀ t ∈ Set.Icc (0 : ℝ) 2, ‖zsCoefficientComplex u z t‖ ≤ C)
    (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 < δ) (haδ : a + δ ≤ 2)
    (hδsmall : δ ≤ 1 / (4 * C + 1))
    (X₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ F : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      F a = X₀ ∧
      ∀ t ∈ Set.Icc a (a + δ),
        HasDerivWithinAt F (zsCoefficientComplex u z t * F t)
          (Set.Icc a (a + δ)) t := by
  obtain ⟨Klip, hLip⟩ :=
    exists_uniform_complexZsVectorField_lipschitzOn_sourcePiNorm_Icc u z hu
  let radius : ℝ≥0 := Real.toNNReal (‖X₀‖ + 1)
  let L : ℝ≥0 := Real.toNNReal (4 * C * (‖X₀‖ + 1))
  have hradius : (radius : ℝ) = ‖X₀‖ + 1 :=
    Real.coe_toNNReal _ (by positivity)
  have hL : (L : ℝ) = 4 * C * (‖X₀‖ + 1) :=
    Real.coe_toNNReal _ (by positivity)
  let t₀ : Set.Icc a (a + δ) :=
    ⟨a, ⟨le_rfl, le_add_of_nonneg_right hδ.le⟩⟩
  let f : ℝ → Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ :=
    fun t X => zsCoefficientComplex u z t * X
  have hpl : IsPicardLindelof f t₀ X₀ radius 0 L Klip := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      have ht₂ : t ∈ Set.Icc (0 : ℝ) 2 :=
        ⟨le_trans ha ht.1, ht.2.trans haδ⟩
      apply LipschitzOnWith.of_dist_le_mul
      intro X _ Y _
      exact (hLip t ht₂).dist_le_mul X Y
    · intro X hX
      have hA := continuousOn_zsCoefficientComplex_any_initial_interval_V4 u z a δ ha hδ.le haδ hu
      exact hA.mul_const X
    · intro t ht X hX
      have ht₂ : t ∈ Set.Icc (0 : ℝ) 2 :=
        ⟨le_trans ha ht.1, ht.2.trans haδ⟩
      have hA : ‖zsCoefficientComplex u z t‖ ≤ C := hCoeff t ht₂
      have hXnorm : ‖X‖ ≤ 2 * (‖X₀‖ + 1) := by
        have hdist : ‖X - X₀‖ ≤ (radius : ℝ) := by
          simpa [dist_eq_norm] using Metric.mem_closedBall.mp hX
        calc
          ‖X‖ = ‖(X - X₀) + X₀‖ := by congr 1 <;> abel
          _ ≤ ‖X - X₀‖ + ‖X₀‖ := norm_add_le _ _
          _ ≤ (radius : ℝ) + ‖X₀‖ := by gcongr
          _ ≤ 2 * (‖X₀‖ + 1) := by rw [hradius]; nlinarith [norm_nonneg X₀]
      calc
        ‖zsCoefficientComplex u z t * X‖ ≤
            2 * ‖zsCoefficientComplex u z t‖ * ‖X‖ :=
          norm_mul_matrix_fin2_le _ _
        _ ≤ 2 * C * ‖X‖ := by gcongr
        _ ≤ 2 * C * (2 * (‖X₀‖ + 1)) := by gcongr
        _ = (L : ℝ) := by rw [hL]; ring
    · change (L : ℝ) * max ((a + δ) - a) (a - a) ≤ (radius : ℝ) - 0
      rw [add_sub_cancel_left, sub_self,
        max_eq_left (show (0 : ℝ) ≤ δ by exact hδ.le), sub_zero, hL, hradius]
      have hproduct : 4 * C * δ ≤ 1 :=
        four_mul_coefficient_mul_step_le_one C δ hC hδ.le hδsmall
      calc
        4 * C * (‖X₀‖ + 1) * δ =
            (‖X₀‖ + 1) * (4 * C * δ) := by ring
        _ ≤ ‖X₀‖ + 1 := by
          exact mul_le_of_le_one_right (by positivity) hproduct
  obtain ⟨F, hF₀, hF⟩ :=
    IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt hpl
      (Metric.mem_closedBall_self (show (0 : ℝ≥0) ≤ 0 by rfl))
  refine ⟨F, ?_, ?_⟩
  · simpa [t₀] using hF₀
  · intro t ht
    set_option backward.isDefEq.respectTransparency false in
      simpa [f] using hF t ht

end NlsGge.SpectralFoundations
