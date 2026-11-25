import NlsGge.Spectral.ComplexZsSourcePiPicardScalarPrerequisitesV3
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

/-- A nonnegative uniform bound for the actual continuous source potential on
its prescribed interval, obtained from compactness rather than added as input
to the E02 theorem. -/
theorem exists_nonneg_actualPotential_norm_bound
    (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖u s‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro s hs
  exact (hC₀ s hs).trans (le_max_left _ _)

end NlsGge.SpectralFoundations
