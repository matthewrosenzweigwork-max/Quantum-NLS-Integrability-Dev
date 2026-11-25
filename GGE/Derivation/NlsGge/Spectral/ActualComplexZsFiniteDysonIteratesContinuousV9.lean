import NlsGge.Spectral.ActualComplexZsCoefficientEntrySupBoundV4
import NlsGge.Spectral.ComplexZsSourcePiPicardScalarPrerequisitesV3
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

/-- The n-th actual ordered Picard/Dyson term, with the recurrence written as
the entry of the actual matrix product under a scalar interval integral. -/
def actualComplexZsDysonTerm (u : ℝ → ℂ) (z : ℂ) : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  | 0, _ => 1
  | n + 1, t => fun i j =>
      ∫ s in (0 : ℝ)..t,
        (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j

theorem continuousOn_actualComplexZsDysonTerm_entry
    (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2)) (z : ℂ)
    (n : ℕ) (i j : Fin 2) :
    ContinuousOn (fun t : ℝ => actualComplexZsDysonTerm u z n t i j)
      (Set.Icc (0 : ℝ) 2) := by
  induction n generalizing i j with
  | zero =>
      simpa [actualComplexZsDysonTerm] using
        (continuousOn_const : ContinuousOn
          (fun _ : ℝ => ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j))
          (Set.Icc (0 : ℝ) 2))
  | succ n ih =>
      change ContinuousOn
        (fun t : ℝ => ∫ s in (0 : ℝ)..t,
          (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j)
        (Set.Icc (0 : ℝ) 2)
      have hprod₀ : ContinuousOn
          (fun s : ℝ => zsCoefficientComplex u z s i 0 *
            actualComplexZsDysonTerm u z n s 0 j)
          (Set.Icc (0 : ℝ) 2) := by
        exact (continuousOn_zsCoefficientComplex_entry u z 2 (by norm_num) hu i 0).mul
          (ih 0 j)
      have hprod₁ : ContinuousOn
          (fun s : ℝ => zsCoefficientComplex u z s i 1 *
            actualComplexZsDysonTerm u z n s 1 j)
          (Set.Icc (0 : ℝ) 2) := by
        exact (continuousOn_zsCoefficientComplex_entry u z 2 (by norm_num) hu i 1).mul
          (ih 1 j)
      have hsum : ContinuousOn
          (fun s : ℝ => zsCoefficientComplex u z s i 0 *
              actualComplexZsDysonTerm u z n s 0 j +
            zsCoefficientComplex u z s i 1 * actualComplexZsDysonTerm u z n s 1 j)
          (Set.Icc (0 : ℝ) 2) := hprod₀.add hprod₁
      have hentry : ContinuousOn
          (fun s : ℝ =>
            (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j)
          (Set.Icc (0 : ℝ) 2) := by
        simpa only [Matrix.mul_apply, Fin.sum_univ_two] using hsum
      have hentry' : ContinuousOn
          (fun s : ℝ =>
            (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j)
          (Set.uIcc (0 : ℝ) 2) := by
        simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hentry
      have hint : IntervalIntegrable
          (fun s : ℝ => (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j)
          MeasureTheory.volume 0 2 := hentry'.intervalIntegrable (μ := MeasureTheory.volume)
      have hzero : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 2 := by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
        exact ⟨le_rfl, by norm_num⟩
      have hprimitive := intervalIntegral.continuousOn_primitive_interval' (μ := MeasureTheory.volume) hint hzero
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hprimitive

end NlsGge.SpectralFoundations

end
