import NlsGge.Hierarchy.RiccatiPeriodicSolutionAsymptotic38
import NlsGge.Hierarchy.RiccatiQuasimomentumCoefficients38
import Mathlib.Tactic

/-! Batch 38, E06.06 formal side, combined: for a smooth period-one field and
every order `K`, the actual periodic Riccati solution `Γ_η` at `ζ = iη` satisfies
`i∫₀¹ uΓ_η = Σ_{m∈Icc 1 K} b_m η^{-m} + O(η^{-K-1})` with
`b_m = riccatiQuasiCoeff38 u m`. This is the hierarchy side of the interface
`k(iη) = iη + Σ b_m η^{-m} + O(η^{-K-1})` agreed with the E02 thread. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open scoped ContDiff

theorem riccatiQuasimomentum_expansion38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (K : ℕ) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η₀ ≤ η → ∃ Γ : ℝ → ℂ, Continuous Γ ∧
      Function.Periodic Γ 1 ∧
      (∀ x, HasDerivAt Γ (-(2 * η) * Γ x + star (u x) - u x * Γ x ^ 2) x) ∧
      ‖Complex.I * (∫ x in (0:ℝ)..1, u x * Γ x) -
        ∑ m ∈ Finset.Icc 1 K, riccatiQuasiCoeff38 u m * (η : ℂ)⁻¹ ^ m‖ ≤ C * η⁻¹ ^ (K + 1) := by
  obtain ⟨η₀, C, hη₀, h⟩ := riccatiPeriodicSolution_asymptotic38 u hu hper K
  obtain ⟨U, hU⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hu.continuous.continuousOn
  set U' := max U 0
  refine ⟨η₀, U' * C, hη₀, fun η hη => ?_⟩
  obtain ⟨Γ, hc, hp, hd, ha⟩ := h η hη
  refine ⟨Γ, hc, hp, hd, ?_⟩
  have := riccati_integral_expansion_Icc38 u hu K η C U' (hη₀.trans_le hη)
    (fun x hx => (hU x hx).trans (le_max_left _ _)) Γ hc ha
  simpa [mul_assoc] using this

end NlsGge.HierarchyRiccati.Core

end
