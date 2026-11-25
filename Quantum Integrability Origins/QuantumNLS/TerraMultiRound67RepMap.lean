import QuantumNLS.TerraMultiRound59FactorLinear

/-! The H¹ continuous representative as a bounded linear map. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open QuantumNLS.Fourier QuantumNLS.TranslatedCorrelation QuantumNLS.TerraMultiRound59FactorLinear
namespace QuantumNLS.TerraMultiRound67RepMap
variable {L : ℝ} [Fact (0 < L)]

def repLinear : Hk L 1 →ₗ[ℂ] C(AddCircle L, ℂ) where
  toFun := contRep (by omega)
  map_add' := contRep_add (by omega)
  map_smul' := contRep_smul (by omega)

def repCLM : Hk L 1 →L[ℂ] C(AddCircle L, ℂ) :=
  repLinear.mkContinuous (cL L) (fun u => by
    change ‖contRep (by omega) u‖ ≤ cL L * ‖u‖
    exact norm_contRep_le (by omega) u)

theorem continuous_rep : Continuous (fun u : Hk L 1 => contRep (by omega) u) :=
  repCLM.continuous

#print axioms repCLM
#print axioms continuous_rep
end QuantumNLS.TerraMultiRound67RepMap
