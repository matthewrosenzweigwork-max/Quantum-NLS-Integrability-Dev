import NlsGge.Spectral.ActualComplexZsDysonSeriesUniformOnDisksV10
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

/-- The entrywise totalized sum of the actual ordered Dyson iterates. -/
def actualComplexZsDysonTsum (u : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ∑' n : ℕ, actualComplexZsDysonTerm u z n t i j

/-- Multiplication by the actual coefficient matrix preserves the pointwise
HasSum of the actual Dyson iterates. The two row contributions use the actual
`(0,j)` and `(1,j)` entry series. -/
theorem hasSum_actualComplexZsDysonProduct_entry
    (u : ℝ → ℂ) (z : ℂ) (R C : ℝ)
    (hz : ‖z‖ ≤ R) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hU : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖u s‖ ≤ C)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 2) (i j : Fin 2) :
    HasSum
      (fun n : ℕ => (zsCoefficientComplex u z s *
        actualComplexZsDysonTerm u z n s) i j)
      ((zsCoefficientComplex u z s * actualComplexZsDysonTsum u z s) i j) := by
  let p : ℂ × ℝ := (z, s)
  have hp : p ∈ {p : ℂ × ℝ | ‖p.1‖ ≤ R ∧ p.2 ∈ Set.Icc (0 : ℝ) 2} :=
    ⟨hz, hs⟩
  have h0 :=
    (hasSumUniformlyOn_actualComplexZsDysonSeries_entry
      u R C hR hC hU 0 j).hasSum hp
  have h1 :=
    (hasSumUniformlyOn_actualComplexZsDysonSeries_entry
      u R C hR hC hU 1 j).hasSum hp
  have hsum := (h0.mul_left (zsCoefficientComplex u z s i 0)).add
    (h1.mul_left (zsCoefficientComplex u z s i 1))
  simpa only [actualComplexZsDysonTsum, Matrix.mul_apply, Fin.sum_univ_two] using hsum

end NlsGge.SpectralFoundations

end
