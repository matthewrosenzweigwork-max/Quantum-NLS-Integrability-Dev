import NlsGge.Spectral.ActualComplexZsDysonFiniteExpansionContinuousPotentialV6
import Mathlib.Analysis.Analytic.Constructions

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

theorem analyticOnNhd_actualComplexZsDysonTerm_of_continuousOn
    (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2))
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun z : ℂ => actualComplexZsDysonTerm u z n t i j) Set.univ := by
  have hpoly : AnalyticOnNhd ℂ
      (∑ k ∈ Finset.range (n + 1),
        fun z : ℂ => z ^ k * actualComplexZsDysonPolynomialCoefficient u n k t i j)
      Set.univ := by
    apply Finset.analyticOnNhd_sum
    intro k hk
    fun_prop
  have hpoly' : AnalyticOnNhd ℂ
      (fun z : ℂ =>
        ∑ k ∈ Finset.range (n + 1),
          z ^ k * actualComplexZsDysonPolynomialCoefficient u n k t i j)
      Set.univ := by
    have hfun :
        (fun z : ℂ =>
          ∑ k ∈ Finset.range (n + 1),
            z ^ k * actualComplexZsDysonPolynomialCoefficient u n k t i j) =
          ∑ k ∈ Finset.range (n + 1),
            fun z : ℂ => z ^ k * actualComplexZsDysonPolynomialCoefficient u n k t i j := by
      funext z
      simp only [Finset.sum_apply]
    rw [hfun]
    exact hpoly
  have heq : (fun z : ℂ => actualComplexZsDysonTerm u z n t i j) =
      fun z : ℂ =>
        ∑ k ∈ Finset.range (n + 1),
          z ^ k * actualComplexZsDysonPolynomialCoefficient u n k t i j := by
    funext z
    exact actualComplexZsDysonTerm_eq_finite_polynomial_of_continuousOn
      u hu z n t ht i j
  rw [heq]
  exact hpoly'

end NlsGge.SpectralFoundations
