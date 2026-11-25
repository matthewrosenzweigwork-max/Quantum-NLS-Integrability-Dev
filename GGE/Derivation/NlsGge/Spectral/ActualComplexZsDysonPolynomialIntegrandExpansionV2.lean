import NlsGge.Spectral.ActualComplexZsDysonPolynomialCoefficientsContinuousV6
import NlsGge.Spectral.ActualComplexZsDysonPolynomialCoefficientSupportV2
import NlsGge.Spectral.ActualComplexZsDysonFinitePolynomialConvolutionV3
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

local instance actualExpansionMatrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedAddCommGroup

local instance actualExpansionMatrixNormedSpace :
    NormedSpace ℂ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedSpace

def actualComplexZsDysonPolynomialPartialSum
    (u : ℝ → ℂ) (z : ℂ) (n : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ∑ k ∈ Finset.range (n + 1),
    z ^ k * actualComplexZsDysonPolynomialCoefficient u n k t i j

theorem actualComplexZsDysonPolynomial_product_eq_recurrence_sum
    (u : ℝ → ℂ) (z : ℂ) (n : ℕ) (s : ℝ) :
    zsCoefficientComplex u z s *
        actualComplexZsDysonPolynomialPartialSum u z n s =
      fun i j => ∑ k ∈ Finset.range (n + 2), z ^ k *
        (∑ l : Fin 2,
          ((zsCoefficientComplex u 0 s i l *
              actualComplexZsDysonPolynomialCoefficient u n k s l j) +
            (if k = 0 then 0 else zsComplexSpectralSlope i l *
              actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j))) := by
  classical
  ext i j
  simp only [Matrix.mul_apply, actualComplexZsDysonPolynomialPartialSum]
  have haff : ∀ l : Fin 2,
      zsCoefficientComplex u z s i l =
        zsCoefficientComplex u 0 s i l + z * zsComplexSpectralSlope i l := by
    intro l
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i l)
      (zsCoefficientComplex_affine_spectral_parameter u z s)
    simpa using h
  simp_rw [haff]
  have hbyl :
      (∑ l : Fin 2,
        ((zsCoefficientComplex u 0 s i l + z * zsComplexSpectralSlope i l) *
          ∑ k ∈ Finset.range (n + 1),
            z ^ k * actualComplexZsDysonPolynomialCoefficient u n k s l j)) =
        ∑ l : Fin 2, ∑ k ∈ Finset.range (n + 2), z ^ k *
          ((zsCoefficientComplex u 0 s i l *
              actualComplexZsDysonPolynomialCoefficient u n k s l j) +
            (if k = 0 then 0 else zsComplexSpectralSlope i l *
              actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j)) := by
    apply Finset.sum_congr rfl
    intro l hl
    symm
    exact actualComplexZsDyson_finite_polynomial_convolution n z
      (zsCoefficientComplex u 0 s i l) (zsComplexSpectralSlope i l)
      (fun k => actualComplexZsDysonPolynomialCoefficient u n k s l j)
      (by
        intro k hk
        exact actualComplexZsDysonPolynomialCoefficient_eq_zero_of_order_lt_degree
          u n k s l j hk)
  rw [hbyl, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.mul_sum]

end NlsGge.SpectralFoundations
