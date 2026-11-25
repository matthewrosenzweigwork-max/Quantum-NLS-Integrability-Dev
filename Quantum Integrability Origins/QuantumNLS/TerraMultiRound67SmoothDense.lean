import QuantumNLS.TerraMultiRound59SmoothDensity
import QuantumNLS.TerraMultiRound59SobolevCoordinates
import QuantumNLS.TerraMultiRound65FourthCore

/-! Density of smooth periodic representatives in the realized H¹ space, and
    uniqueness of a continuous extension from these representatives. -/
set_option autoImplicit false
noncomputable section
open QuantumNLS.ClassicalCharges QuantumNLS.TranslatedCorrelation
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc QuantumNLS.TerraMultiRound59SobolevCoordinates
open QuantumNLS.TerraMultiRound59SmoothDensity QuantumNLS.TerraMultiRound59RCompatibility
open QuantumNLS.TerraMultiRound65FourthCore
namespace QuantumNLS.TerraMultiRound67SmoothDense
variable {L : ℝ} [Fact (0 < L)]

def smoothFields : Set (Hk L 1) :=
  {u | SmoothPeriodic L (physRep L 1 (coordinates (L := L) 1 u))}

theorem dense_smoothFields : Dense (smoothFields (L := L)) := by
  exact (dense_smooth L 1).preimage (coordinates (L := L) 1).toHomeomorph.isOpenMap

theorem continuous_candidate_eq_Rfield (κ : ℝ) (hκ : 0 < κ) (F : Hk L 1 → ℝ)
    (hF : Continuous F)
    (hsmooth : ∀ u ∈ smoothFields (L := L), F u = Rfield (L := L) 2 (by omega) κ u) :
    F = Rfield (L := L) 2 (by omega) κ := by
  exact Continuous.ext_on dense_smoothFields hF (fourth_order_core L κ hκ).2.1 hsmooth

#print axioms dense_smoothFields
#print axioms continuous_candidate_eq_Rfield
end QuantumNLS.TerraMultiRound67SmoothDense
