import NlsGge.Spectral.ActualComplexZsCoefficientEntireInSpectralParameterV1
import NlsGge.Spectral.ComplexZsSourcePiPicardScalarPrerequisitesV3
import NlsGge.Spectral.ActualComplexPointwiseContinuousMulAddPrerequisiteV1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

/-- Time-dependent scalar coefficients for the actual finite Dyson polynomial
in z. The recurrence is the coefficient convolution for
`A(z,s)=A(0,s)+z•zsComplexSpectralSlope`. -/
def actualComplexZsDysonPolynomialCoefficient (u : ℝ → ℂ) :
    ℕ → ℕ → ℝ → Fin 2 → Fin 2 → ℂ
  | 0, k, _, i, j => if k = 0 then (1 : Matrix (Fin 2) (Fin 2) ℂ) i j else 0
  | n + 1, k, t, i, j =>
      ∫ s in (0 : ℝ)..t,
        ∑ l : Fin 2, ((
          (zsCoefficientComplex u 0 s i l *
            actualComplexZsDysonPolynomialCoefficient u n k s l j) +
          (if k = 0 then 0 else
            zsComplexSpectralSlope i l *
              actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j)))

theorem continuousOn_actualComplexZsDysonPolynomialCoefficient
    (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2))
    (n k : ℕ) (i j : Fin 2) :
    ContinuousOn
      (fun t : ℝ => actualComplexZsDysonPolynomialCoefficient u n k t i j)
      (Set.Icc (0 : ℝ) 2) := by
  induction n generalizing k i j with
  | zero =>
      simp only [actualComplexZsDysonPolynomialCoefficient]
      split_ifs <;> exact continuousOn_const
  | succ n ih =>
      change ContinuousOn
        (fun t : ℝ => ∫ s in (0 : ℝ)..t,
          ∑ l : Fin 2, ((
            (zsCoefficientComplex u 0 s i l *
              actualComplexZsDysonPolynomialCoefficient u n k s l j) +
            (if k = 0 then 0 else
              zsComplexSpectralSlope i l *
                actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j))))
        (Set.Icc (0 : ℝ) 2)
      have hsum : ContinuousOn
          (fun s : ℝ =>
            ∑ l : Fin 2, ((
              (zsCoefficientComplex u 0 s i l *
                actualComplexZsDysonPolynomialCoefficient u n k s l j) +
              (if k = 0 then 0 else
                zsComplexSpectralSlope i l *
                  actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j))))
          (Set.Icc (0 : ℝ) 2) := by
        apply continuousOn_finsetSum (Finset.univ : Finset (Fin 2))
        intro l hl
        have hA : ContinuousOn (fun s : ℝ => zsCoefficientComplex u 0 s i l)
            (Set.Icc (0 : ℝ) 2) :=
          continuousOn_zsCoefficientComplex_entry u 0 2 (by norm_num) hu i l
        have hC : ContinuousOn
            (fun s : ℝ => actualComplexZsDysonPolynomialCoefficient u n k s l j)
            (Set.Icc (0 : ℝ) 2) := ih k l j
        by_cases hk : k = 0
        · have hC0 : ContinuousOn
              (fun s : ℝ => actualComplexZsDysonPolynomialCoefficient u n 0 s l j)
              (Set.Icc (0 : ℝ) 2) := by simpa [hk] using hC
          simpa [hk] using continuousOn_complex_pointwise_mul
            (Set.Icc (0 : ℝ) 2)
            (fun s : ℝ => zsCoefficientComplex u 0 s i l)
            (fun s : ℝ => actualComplexZsDysonPolynomialCoefficient u n 0 s l j)
            hA hC0
        · have hB : ContinuousOn
              (fun _ : ℝ => zsComplexSpectralSlope i l) (Set.Icc (0 : ℝ) 2) :=
            continuousOn_const
          have hC' : ContinuousOn
              (fun s : ℝ => actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j)
              (Set.Icc (0 : ℝ) 2) := ih (k - 1) l j
          have hresult := continuousOn_complex_pointwise_mul_add
            (Set.Icc (0 : ℝ) 2)
            (fun s : ℝ => zsCoefficientComplex u 0 s i l)
            (fun s : ℝ => actualComplexZsDysonPolynomialCoefficient u n k s l j)
            (fun _ : ℝ => zsComplexSpectralSlope i l)
            (fun s : ℝ => actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j)
            hA hC hB hC'
          simpa only [if_neg hk] using hresult
      have hsum' : ContinuousOn
          (fun s : ℝ =>
            ∑ l : Fin 2, ((
              (zsCoefficientComplex u 0 s i l *
                actualComplexZsDysonPolynomialCoefficient u n k s l j) +
              (if k = 0 then 0 else
                zsComplexSpectralSlope i l *
                  actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j))))
          (Set.uIcc (0 : ℝ) 2) := by
        simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hsum
      have hint : IntervalIntegrable
          (fun s : ℝ => ∑ l : Fin 2, ((zsCoefficientComplex u 0 s i l *
            actualComplexZsDysonPolynomialCoefficient u n k s l j) +
            (if k = 0 then 0 else zsComplexSpectralSlope i l *
              actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j)))
          MeasureTheory.volume 0 2 := hsum'.intervalIntegrable (μ := MeasureTheory.volume)
      have hzero : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 2 := by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
        exact ⟨le_rfl, by norm_num⟩
      have hprimitive := intervalIntegral.continuousOn_primitive_interval' (μ := MeasureTheory.volume) hint hzero
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hprimitive

end NlsGge.SpectralFoundations

end
