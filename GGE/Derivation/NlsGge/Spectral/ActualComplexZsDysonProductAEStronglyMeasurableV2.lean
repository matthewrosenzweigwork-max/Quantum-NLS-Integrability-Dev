import NlsGge.Spectral.ActualComplexZsFiniteDysonIteratesContinuousV9
import NlsGge.Spectral.ActualComplexZsDysonPolynomialCoefficientsContinuousV6
import NlsGge.Spectral.ActualComplexPointwiseContinuousMulAddPrerequisiteV1
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

/-- The actual matrix-product entry in the Dyson recurrence is strongly
measurable on the restricted source interval. -/
theorem aestronglyMeasurable_actualComplexZsDysonProductEntryOnIoc
    (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2))
    (z : ℂ) (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2)
    (i j : Fin 2) :
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)) := by
  have hA0 : ContinuousOn (fun s : ℝ => zsCoefficientComplex u z s i 0)
      (Set.Icc (0 : ℝ) 2) :=
    continuousOn_zsCoefficientComplex_entry u z 2 (by norm_num) hu i 0
  have hA1 : ContinuousOn (fun s : ℝ => zsCoefficientComplex u z s i 1)
      (Set.Icc (0 : ℝ) 2) :=
    continuousOn_zsCoefficientComplex_entry u z 2 (by norm_num) hu i 1
  have hD0 : ContinuousOn (fun s : ℝ => actualComplexZsDysonTerm u z n s 0 j)
      (Set.Icc (0 : ℝ) 2) :=
    continuousOn_actualComplexZsDysonTerm_entry u hu z n 0 j
  have hD1 : ContinuousOn (fun s : ℝ => actualComplexZsDysonTerm u z n s 1 j)
      (Set.Icc (0 : ℝ) 2) :=
    continuousOn_actualComplexZsDysonTerm_entry u hu z n 1 j
  have hprod0 := continuousOn_complex_pointwise_mul
    (Set.Icc (0 : ℝ) 2)
    (fun s : ℝ => zsCoefficientComplex u z s i 0)
    (fun s : ℝ => actualComplexZsDysonTerm u z n s 0 j) hA0 hD0
  have hprod1 := continuousOn_complex_pointwise_mul
    (Set.Icc (0 : ℝ) 2)
    (fun s : ℝ => zsCoefficientComplex u z s i 1)
    (fun s : ℝ => actualComplexZsDysonTerm u z n s 1 j) hA1 hD1
  have hcont : ContinuousOn
      (fun s : ℝ => (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j)
      (Set.Icc (0 : ℝ) 2) := by
    simpa only [Matrix.mul_apply, Fin.sum_univ_two] using! hprod0.add hprod1
  have hsubset : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) 2 := by
    intro s hs
    exact ⟨le_of_lt hs.1, le_trans hs.2 ht.2⟩
  exact hcont.aestronglyMeasurable_of_subset_isCompact
    isCompact_Icc measurableSet_Ioc hsubset

end NlsGge.SpectralFoundations
