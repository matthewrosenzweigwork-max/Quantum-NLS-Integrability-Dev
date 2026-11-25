import NlsGge.Spectral.ActualComplexZsDysonPolynomialCoefficientsContinuousV6
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

theorem actualComplexZsDysonPolynomialCoefficient_eq_zero_of_order_lt_degree
    (u : ℝ → ℂ) (n k : ℕ) (t : ℝ) (i j : Fin 2)
    (h : n < k) :
    actualComplexZsDysonPolynomialCoefficient u n k t i j = 0 := by
  induction n generalizing k t i j with
  | zero =>
      have hk : k ≠ 0 := by omega
      simp [actualComplexZsDysonPolynomialCoefficient, hk]
  | succ n ih =>
      have hk₀ : n < k := by omega
      have hk₁ : n < k - 1 := by omega
      have hkne : k ≠ 0 := by omega
      simp only [actualComplexZsDysonPolynomialCoefficient]
      have hfun : (fun s : ℝ =>
          ∑ l : Fin 2, ((zsCoefficientComplex u 0 s i l *
              actualComplexZsDysonPolynomialCoefficient u n k s l j) +
            (if k = 0 then 0 else zsComplexSpectralSlope i l *
              actualComplexZsDysonPolynomialCoefficient u n (k - 1) s l j))) =
          fun _ => (0 : ℂ) := by
        funext s
        apply Finset.sum_eq_zero
        intro l hl
        simp [hkne, ih k s l j hk₀, ih (k - 1) s l j hk₁]
      rw [hfun]
      simp

end NlsGge.SpectralFoundations
