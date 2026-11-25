import QuantumNLS.Local002Discharge

/-! Actual LOCAL-003 projection rank, on the small physical-field ball.
This is not spectral multiplicity or the arbitrary-field construction. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
namespace QuantumNLS.TerraMultiRound32LocalRank
open QuantumNLS.LocalSpectral QuantumNLS.Local002
open QuantumNLS.Local002Free QuantumNLS.Local002Discharge
variable {L κ : ℝ}

/-- The actual free contour projection has rank two, and the actual
perturbed contour projections have rank two on one label-independent ball. -/
theorem actual_base_and_nearby_rank_two (hL : 0 < L) {r : ℝ}
    (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
    (∀ n : ℤ, Module.finrank ℂ (rng (freeProj L κ n r)) = 2) ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℤ,
      (∀ u : Lp ℂ 2 (μI L), ‖u‖ < ρ →
        Module.finrank ℂ (rng (perturbedProj L κ (u : ℝ → ℂ) n r)) = 2) ∧
      AnalyticOnNhd ℝ (fun u : Lp ℂ 2 (μI L) =>
        perturbedProj L κ (u : ℝ → ℂ) n r) (ball 0 ρ) := by
  constructor
  · intro n
    exact finrank_freeProj hL hr hr2 n
      (fun z hz => (free_resolvent_hyp L κ).res r n z hr hr2 hz)
  · obtain ⟨ρ, hρ, C, h⟩ := reset_analytic_projections (L := L) (κ := κ) hL hr hr2
    refine ⟨ρ, hρ, fun n => ⟨?_, (h n).2⟩⟩
    intro u hu
    exact ((h n).1 u hu).2.2.1

end QuantumNLS.TerraMultiRound32LocalRank
#print axioms QuantumNLS.TerraMultiRound32LocalRank.actual_base_and_nearby_rank_two
