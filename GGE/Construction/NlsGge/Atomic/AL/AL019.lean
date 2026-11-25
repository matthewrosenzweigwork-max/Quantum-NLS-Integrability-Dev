import NlsGge.Hierarchy.ALPoissonLiouville38

namespace NlsGge.Atomic.AL019

open NlsGge.AblowitzLadik

theorem alLiouvilleDensity_exact38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) :
    alRho38 α = ∏ j : ZMod L, (1 - ‖α j‖ ^ 2)⁻¹ := rfl

theorem alWeightedField_exact38 {L : ℕ} [NeZero L] (H : (ZMod L → ℂ) → ℝ)
    (α : ZMod L → ℂ) :
    alRhoX38 H α = (alRho38 α) • alX38 H α := by
  funext j
  simp [alRhoX38, Complex.real_smul]

theorem alHamiltonian_weighted_divergence_zero
    {L : ℕ} [NeZero L]
    {H : (ZMod L → ℂ) → ℝ}
    (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alDiv38 (alRhoX38 H) α = 0 :=
  alLiouville38 hH hα

end NlsGge.Atomic.AL019
