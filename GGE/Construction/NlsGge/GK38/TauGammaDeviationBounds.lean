import NlsGge.GK38.TauGammaExterior

/-! A common local bound controls both actual Hilbert perturbation norms. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem periodic_deviation_norms_local38 (φ₀ : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ φ ∈ U,
      ‖periodicPlusDeviation38 φ‖ ≤ K ∧ ‖periodicMinusDeviation38 φ‖ ≤ K := by
  obtain ⟨U, hU, B, hB, h⟩ := periodic_l2_summable38 φ₀
  refine ⟨U, hU, B + 1, by positivity, fun φ hφ => ?_⟩
  have hp : ‖periodicPlusDeviation38 φ‖ ^ 2 ≤ B := by
    rw [periodicPlusDeviation38, l2SequenceOf_norm_sq38 _ (periodic_plus_summable38 φ)]
    exact ((periodic_plus_summable38 φ).tsum_le_tsum
      (fun n => le_add_of_nonneg_left (sq_nonneg _)) (h φ hφ).1).trans (h φ hφ).2
  have hm : ‖periodicMinusDeviation38 φ‖ ^ 2 ≤ B := by
    rw [periodicMinusDeviation38, l2SequenceOf_norm_sq38 _ (periodic_minus_summable38 φ)]
    exact ((periodic_minus_summable38 φ).tsum_le_tsum
      (fun n => le_add_of_nonneg_right (sq_nonneg _)) (h φ hφ).1).trans (h φ hφ).2
  constructor <;> nlinarith [norm_nonneg (periodicPlusDeviation38 φ),
    norm_nonneg (periodicMinusDeviation38 φ), sq_nonneg B]

end
end NlsGge.GK38
