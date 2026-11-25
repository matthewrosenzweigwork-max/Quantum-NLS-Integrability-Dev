import NlsGge.Spectral.ActualComplexZsFiniteDysonIteratesContinuousV9
import NlsGge.Spectral.ActualComplexZsDysonPolynomialIntegrandExpansionV2
import NlsGge.Spectral.ActualComplexZsDysonCoefficientRecurrenceIntegrableV3
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

theorem actualComplexZsDysonTerm_eq_finite_polynomial_of_continuousOn
    (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2))
    (z : ℂ) (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2)
    (i j : Fin 2) :
    actualComplexZsDysonTerm u z n t i j =
      ∑ k ∈ Finset.range (n + 1),
        z ^ k * actualComplexZsDysonPolynomialCoefficient u n k t i j := by
  induction n generalizing t i j with
  | zero =>
      simp [actualComplexZsDysonTerm, actualComplexZsDysonPolynomialCoefficient]
  | succ n ih =>
      change (∫ s in (0 : ℝ)..t,
          (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j) =
        ∑ k ∈ Finset.range (n + 2),
          z ^ k * actualComplexZsDysonPolynomialCoefficient u (n + 1) k t i j
      have hsubset : Set.uIcc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) 2 := by
        rw [Set.uIcc_of_le ht.1]
        rintro s ⟨hs0, hst⟩
        exact ⟨hs0, le_trans hst ht.2⟩
      have hpoint : ∀ s ∈ Set.uIcc (0 : ℝ) t,
          (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j =
            ∑ k ∈ Finset.range (n + 2), z ^ k *
              (∑ l : Fin 2,
                ((zsCoefficientComplex u 0 s i l *
                    actualComplexZsDysonPolynomialCoefficient u n k s l j) +
                  (if k = 0 then 0 else zsComplexSpectralSlope i l *
                    actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j))) := by
        intro s hs
        have hmatrix : actualComplexZsDysonTerm u z n s =
            actualComplexZsDysonPolynomialPartialSum u z n s := by
          ext a b
          simpa [actualComplexZsDysonPolynomialPartialSum] using
            ih s (hsubset hs) a b
        calc
          (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j =
              (zsCoefficientComplex u z s *
                actualComplexZsDysonPolynomialPartialSum u z n s) i j :=
            congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ =>
              (zsCoefficientComplex u z s * M) i j) hmatrix
          _ = ∑ k ∈ Finset.range (n + 2), z ^ k *
                (∑ l : Fin 2,
                  ((zsCoefficientComplex u 0 s i l *
                      actualComplexZsDysonPolynomialCoefficient u n k s l j) +
                    (if k = 0 then 0 else zsComplexSpectralSlope i l *
                      actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j))) :=
            congrFun (congrFun
              (actualComplexZsDysonPolynomial_product_eq_recurrence_sum u z n s) i) j
      have hint : ∀ k ∈ Finset.range (n + 2),
          IntervalIntegrable
            (fun s : ℝ => z ^ k *
              (∑ l : Fin 2,
                ((zsCoefficientComplex u 0 s i l *
                    actualComplexZsDysonPolynomialCoefficient u n k s l j) +
                  (if k = 0 then 0 else zsComplexSpectralSlope i l *
                    actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j))))
            MeasureTheory.volume 0 t := by
        intro k hk
        exact (intervalIntegrable_actualComplexZsDysonCoefficientRecurrenceIntegrand
          u hu n k t ht i j).const_mul (z ^ k)
      calc
        actualComplexZsDysonTerm u z (n + 1) t i j =
            ∫ s in (0 : ℝ)..t,
              (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j := rfl
        _ = ∫ s in (0 : ℝ)..t,
              ∑ k ∈ Finset.range (n + 2), z ^ k *
                (∑ l : Fin 2,
                  ((zsCoefficientComplex u 0 s i l *
                      actualComplexZsDysonPolynomialCoefficient u n k s l j) +
                    (if k = 0 then 0 else zsComplexSpectralSlope i l *
                      actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j))) :=
              intervalIntegral.integral_congr hpoint
        _ = ∑ k ∈ Finset.range (n + 2),
              ∫ s in (0 : ℝ)..t, z ^ k *
                (∑ l : Fin 2,
                  ((zsCoefficientComplex u 0 s i l *
                      actualComplexZsDysonPolynomialCoefficient u n k s l j) +
                    (if k = 0 then 0 else zsComplexSpectralSlope i l *
                      actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j))) :=
              intervalIntegral.integral_finsetSum hint
        _ = ∑ k ∈ Finset.range (n + 2),
              z ^ k * (∫ s in (0 : ℝ)..t,
                ∑ l : Fin 2,
                  ((zsCoefficientComplex u 0 s i l *
                      actualComplexZsDysonPolynomialCoefficient u n k s l j) +
                    (if k = 0 then 0 else zsComplexSpectralSlope i l *
                      actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j))) := by
              simp_rw [intervalIntegral.integral_const_mul]
        _ = ∑ k ∈ Finset.range (n + 2),
              z ^ k * actualComplexZsDysonPolynomialCoefficient u (n + 1) k t i j := by
              simp only [actualComplexZsDysonPolynomialCoefficient]

end NlsGge.SpectralFoundations
