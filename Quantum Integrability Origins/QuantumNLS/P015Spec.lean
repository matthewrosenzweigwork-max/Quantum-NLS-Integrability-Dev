import QuantumNLS.Prop015Main
/-! integrator-authored trusted spec for PROP-015 Q7A:lem:interp (review record r48/r49 PASS): headline statement(s) copied verbatim from Prop015Main (QuantumNLS.Prop015Main). -/

namespace QuantumNLS.P015Spec
open QuantumNLS.Prop015Main
open Finset
open QuantumNLS.Interpolation

set_option maxHeartbeats 8000000 in
theorem interpolation_lemma_spec {m : ℕ} (zs : Fin (m + 1) → ℂ)
    (hz : Function.Injective zs) (H H1 : ℝ) :
    (∀ q z : ℂ, (∀ j, zs j ≠ q) → z ≠ q →
      1 / (z - q) - ∑ j, lagrangeValue zs j z / (zs j - q) =
        (-1) ^ (m + 1) * (∏ j, (z - zs j)) / ((z - q) * ∏ j, (zs j - q))) ∧
    (∃ C R0 : ℝ, ∀ (q z a : ℂ) (R : ℝ), R0 ≤ R →
      ‖z - a‖ ≤ H → (∀ j, ‖zs j - a‖ ≤ H1) → ‖q‖ ≤ R → 2 * R ≤ ‖a‖ →
      ‖(-1 : ℂ) ^ (m + 1) * (∏ j, (z - zs j)) / ((z - q) * ∏ j, (zs j - q))‖
        ≤ C / R ^ (m + 2)) := by
  exact QuantumNLS.Prop015Main.interpolation_lemma zs hz H H1

end QuantumNLS.P015Spec
#print axioms QuantumNLS.P015Spec.interpolation_lemma_spec
