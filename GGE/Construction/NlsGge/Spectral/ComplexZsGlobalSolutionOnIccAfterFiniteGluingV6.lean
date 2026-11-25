import NlsGge.Spectral.ComplexZsFiniteIntervalSolutionGluingV5
import NlsGge.Spectral.ComplexZsSourcePiNormLipschitzAfterNNRealPrerequisiteV2
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

local instance globalMatrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) :=
  instAnyInitialSourcePiNormedAddCommGroup

local instance globalMatrixNormedSpace :
    NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  instAnyInitialSourcePiNormedSpace

/-- Finite equal-step continuation of the actual complex-parameter ZS matrix ODE. -/
theorem exists_global_complexZs_matrix_solution_on_Icc_V1
    (u : ℝ → ℂ) (z : ℂ)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2))
    (X₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ F : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      F 0 = X₀ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 2,
        HasDerivWithinAt F (zsCoefficientComplex u z t * F t)
          (Set.Icc (0 : ℝ) 2) t := by
  obtain ⟨C, hC, hCoeff⟩ := exists_bound_zsCoefficientComplex_sourcePiNorm u z hu
  have hden : 0 < 4 * C + 1 := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (4 * C + 1))
  have hNpos : 0 < (N : ℝ) := by
    have hleft : 0 < 2 * (4 * C + 1) := by positivity
    exact lt_trans hleft hN
  let step : ℝ := 2 / (N : ℝ)
  have hstep : 0 < step := by
    dsimp [step]
    exact div_pos (by norm_num) hNpos
  have hNstep : (N : ℝ) * step = 2 := by
    dsimp [step]
    field_simp [ne_of_gt hNpos]
  have hstepSmall : step ≤ 1 / (4 * C + 1) := by
    dsimp [step]
    apply (div_le_iff₀ hNpos).2
    calc
      2 ≤ (N : ℝ) / (4 * C + 1) :=
        (le_div_iff₀ hden).2 hN.le
      _ = (1 / (4 * C + 1)) * (N : ℝ) := by ring
  have hbuild :
      ∀ k : ℕ, 1 ≤ k → k ≤ N →
        ∃ F : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
          F 0 = X₀ ∧
          ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) * step),
            HasDerivWithinAt F (zsCoefficientComplex u z t * F t)
              (Set.Icc (0 : ℝ) ((k : ℝ) * step)) t := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk1 hkN
      cases k with
      | zero => omega
      | succ k =>
        cases k with
        | zero =>
          have hstepLeTwo : step ≤ 2 := by
            calc
              step = (1 : ℝ) * step := by ring
              _ ≤ (N : ℝ) * step :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hkN) hstep.le
              _ = 2 := hNstep
          obtain ⟨F, hinit, hderiv⟩ :=
            exists_local_complexZs_matrix_solution_from_any_sourcePi_initial_state_V4
              u z hu C hC hCoeff 0 step (by norm_num) hstep (by simpa using hstepLeTwo)
              hstepSmall X₀
          refine ⟨F, hinit, ?_⟩
          simpa using hderiv
        | succ m =>
          have hprev1 : 1 ≤ m + 1 := by omega
          have hprevN : m + 1 ≤ N := by omega
          obtain ⟨F, hinit, hFderiv⟩ := ih (m + 1) (by omega) hprev1 hprevN
          let b : ℝ := ((m + 1 : ℕ) : ℝ) * step
          let c : ℝ := ((m + 2 : ℕ) : ℝ) * step
          have hbc : b + step = c := by
            dsimp [b, c]
            push_cast
            ring
          have hb : 0 ≤ b := by
            dsimp [b]
            positivity
          have hcLeTwo : c ≤ 2 := by
            dsimp [c]
            rw [← hNstep]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkN) hstep.le
          obtain ⟨G, hGb, hGderiv⟩ :=
            exists_local_complexZs_matrix_solution_from_any_sourcePi_initial_state_V4
              u z hu C hC hCoeff b step hb hstep (by rw [hbc]; exact hcLeTwo)
              hstepSmall (F b)
          have hFderiv' : ∀ t ∈ Set.Icc (0 : ℝ) b,
              HasDerivWithinAt F (zsCoefficientComplex u z t * F t)
                (Set.Icc (0 : ℝ) b) t := by
            simpa [b] using hFderiv
          have hGderiv' : ∀ t ∈ Set.Icc b c,
              HasDerivWithinAt G (zsCoefficientComplex u z t * G t)
                (Set.Icc b c) t := by
            simpa [hbc] using hGderiv
          let H : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t => if t ≤ b then F t else G t
          have hstart : H 0 = X₀ := by
            have hzero : (0 : ℝ) ≤ b := hb
            simp [H, hzero, hinit]
          have hjoined : ∀ t ∈ Set.Icc (0 : ℝ) c,
              HasDerivWithinAt H (zsCoefficientComplex u z t * H t)
                (Set.Icc (0 : ℝ) c) t := by
            simpa [H] using
              (hasDerivWithinAt_glue_adjacent_Icc
                (fun t X => zsCoefficientComplex u z t * X)
                0 b c (by exact hb) (by rw [← hbc]; exact le_add_of_nonneg_right hstep.le)
                F G hGb.symm hFderiv' hGderiv')
          refine ⟨H, hstart, ?_⟩
          simpa [c, Nat.cast_add, Nat.cast_one, Nat.add_assoc] using hjoined
  obtain ⟨F, hinit, hderiv⟩ := hbuild N (by exact_mod_cast hNpos) (le_rfl)
  refine ⟨F, hinit, ?_⟩
  simpa [hNstep] using hderiv

end NlsGge.SpectralFoundations

end
