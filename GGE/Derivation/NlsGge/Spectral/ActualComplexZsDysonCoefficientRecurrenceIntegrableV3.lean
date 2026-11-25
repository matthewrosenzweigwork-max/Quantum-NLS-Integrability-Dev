import NlsGge.Spectral.ActualComplexZsDysonPolynomialCoefficientsContinuousV6
import NlsGge.Spectral.ActualComplexPointwiseContinuousMulAddPrerequisiteV1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

/-- The actual coefficient-recurrence integrand is continuous on the source
interval for a continuous actual potential. -/
theorem continuousOn_actualComplexZsDysonCoefficientRecurrenceIntegrand
    (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2))
    (n k : ℕ) (i j : Fin 2) :
    ContinuousOn
      (fun s : ℝ => ∑ l : Fin 2,
        ((zsCoefficientComplex u 0 s i l *
            actualComplexZsDysonPolynomialCoefficient u n k s l j) +
          (if k = 0 then 0 else zsComplexSpectralSlope i l *
            actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j)))
      (Set.Icc (0 : ℝ) 2) := by
  classical
  apply continuousOn_finsetSum (Finset.univ : Finset (Fin 2))
  intro l hl
  have hA : ContinuousOn (fun s : ℝ => zsCoefficientComplex u 0 s i l)
      (Set.Icc (0 : ℝ) 2) :=
    continuousOn_zsCoefficientComplex_entry u 0 2 (by norm_num) hu i l
  have hC : ContinuousOn
      (fun s : ℝ => actualComplexZsDysonPolynomialCoefficient u n k s l j)
      (Set.Icc (0 : ℝ) 2) :=
    continuousOn_actualComplexZsDysonPolynomialCoefficient u hu n k l j
  by_cases hk : k = 0
  · simpa only [if_pos hk, add_zero] using
      continuousOn_complex_pointwise_mul (Set.Icc (0 : ℝ) 2)
        (fun s : ℝ => zsCoefficientComplex u 0 s i l)
        (fun s : ℝ => actualComplexZsDysonPolynomialCoefficient u n k s l j) hA hC
  · have hB : ContinuousOn (fun _ : ℝ => zsComplexSpectralSlope i l)
        (Set.Icc (0 : ℝ) 2) := continuousOn_const
    have hC' : ContinuousOn
        (fun s : ℝ => actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j)
        (Set.Icc (0 : ℝ) 2) :=
      continuousOn_actualComplexZsDysonPolynomialCoefficient u hu n (k - 1) l j
    simpa only [if_neg hk] using
      continuousOn_complex_pointwise_mul_add
        (Set.Icc (0 : ℝ) 2)
        (fun s : ℝ => zsCoefficientComplex u 0 s i l)
        (fun s : ℝ => actualComplexZsDysonPolynomialCoefficient u n k s l j)
        (fun _ : ℝ => zsComplexSpectralSlope i l)
        (fun s : ℝ => actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j)
        hA hC hB hC'

/-- On any source subinterval `[0,t]`, the coefficient recurrence can be
integrated. -/
theorem intervalIntegrable_actualComplexZsDysonCoefficientRecurrenceIntegrand
    (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2))
    (n k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2)
    (i j : Fin 2) :
    IntervalIntegrable
      (fun s : ℝ => ∑ l : Fin 2,
        ((zsCoefficientComplex u 0 s i l *
            actualComplexZsDysonPolynomialCoefficient u n k s l j) +
          (if k = 0 then 0 else zsComplexSpectralSlope i l *
            actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j)))
      MeasureTheory.volume 0 t := by
  have hcont := continuousOn_actualComplexZsDysonCoefficientRecurrenceIntegrand
    u hu n k i j
  have hsubset : Set.uIcc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) 2 := by
    rw [Set.uIcc_of_le ht.1]
    rintro s ⟨hs0, hst⟩
    exact ⟨hs0, le_trans hst ht.2⟩
  exact (hcont.mono hsubset).intervalIntegrable (μ := MeasureTheory.volume)

end NlsGge.SpectralFoundations
