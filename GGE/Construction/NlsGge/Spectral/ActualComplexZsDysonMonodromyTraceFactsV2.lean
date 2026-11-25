import NlsGge.Spectral.ActualComplexZsDysonVolterraWithinODEV3
import NlsGge.Spectral.ActualComplexZsDysonTsumEntireContinuousPotentialV6

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

/-- The actual continuous-potential Dyson fundamental matrix has identity
initial data and determinant one throughout the source interval. Its
identification with the normalized ODE fundamental matrix is supplied by the
Volterra/uniqueness theorem, with no L²-potential conclusion asserted. -/
theorem actualComplexZsDysonTsum_initial_and_determinant_of_continuousOn
    (u : ℝ → ℂ) (z : ℂ)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2)) :
    actualComplexZsDysonTsum u z 0 = 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 2,
        Matrix.det (actualComplexZsDysonTsum u z t) = 1 := by
  obtain ⟨G, hG0, hG, hdet, hEq⟩ :=
    exists_normalized_actualComplexZsDysonFundamental_Icc u z hu
  constructor
  · have hEq0 := hEq (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 2)
    change G 0 = actualComplexZsDysonTsum u z 0 at hEq0
    calc
      actualComplexZsDysonTsum u z 0 = G 0 := hEq0.symm
      _ = 1 := hG0
  · intro t ht
    have hEqT := hEq ht
    change G t = actualComplexZsDysonTsum u z t at hEqT
    calc
      Matrix.det (actualComplexZsDysonTsum u z t) = Matrix.det (G t) :=
        congrArg Matrix.det hEqT.symm
      _ = 1 := hdet t ht

/-- The full unit-period monodromy trace is entire for every actual continuous
potential. This is the trace of `F(1)`; the independently defined doubled
period trace remains a different quantity. -/
theorem analyticOnNhd_actualComplexZsDysonUnitMonodromyTrace_of_continuousOn
    (u : ℝ → ℂ)
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2)) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => Matrix.trace (actualComplexZsDysonTsum u z 1)) Set.univ := by
  have h00 := analyticOnNhd_actualComplexZsDysonTsum_of_continuousOn
    u hu 1 (by norm_num) 0 0
  have h11 := analyticOnNhd_actualComplexZsDysonTsum_of_continuousOn
    u hu 1 (by norm_num) 1 1
  simpa only [Matrix.trace_fin_two, actualComplexZsDysonTsum, Pi.add_apply] using!
    h00.add h11

end NlsGge.SpectralFoundations

end
