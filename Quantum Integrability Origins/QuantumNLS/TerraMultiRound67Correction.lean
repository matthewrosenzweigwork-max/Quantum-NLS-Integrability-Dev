import QuantumNLS.TerraMultiRound67DensityCandidate
import QuantumNLS.TerraMultiRound67Sextic

/-! Explicit continuous H¹ correction candidate. The remaining product rule
    and smooth identification are not assumed by these statements. -/
set_option autoImplicit false
noncomputable section
open QuantumNLS.TranslatedCorrelation QuantumNLS.TerraMultiRound67Quartic
open QuantumNLS.TerraMultiRound67DensityCandidate QuantumNLS.TerraMultiRound67Sextic
namespace QuantumNLS.TerraMultiRound67Correction
variable {L : ℝ} [Fact (0 < L)]

def correction (κ : ℝ) (u : Hk L 1) : ℝ :=
  κ * (6 * ‖weightedDerivative u‖^2 + ‖densityCandidate u‖^2) + 2 * κ^2 * sexticIntegral u

theorem continuous_correction (κ : ℝ) : Continuous (correction (L := L) κ) := by
  unfold correction
  exact (continuous_const.mul ((continuous_const.mul
    ((continuous_weightedDerivative (L := L)).norm.pow 2)).add
    (continuous_densityCandidate_sq (L := L)))).add
    (continuous_const.mul (continuous_sexticIntegral (L := L)))

#print axioms continuous_correction
end QuantumNLS.TerraMultiRound67Correction
