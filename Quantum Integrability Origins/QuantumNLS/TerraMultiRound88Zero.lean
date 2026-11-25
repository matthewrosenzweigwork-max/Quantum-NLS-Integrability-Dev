import QuantumNLS.Prop001RseventeenZero
import QuantumNLS.Prop025OInputs

/-! The rank-zero marginal is the scalar vacuum, for every normalized
N-particle vector and every one-particle profile. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound88Zero
open TensorCarrier PhysicalTensor
variable {L : ℝ} [Fact (0 < L)]

theorem rank_zero_marginal (N : ℕ) (ψ : HilbertTensorPower ℂ (L2T L) N)
    (hψ : ‖ψ‖ = 1) (u : L2T L) :
    reducedDensityN N 0 (Nat.zero_le N) ψ = Prop025OInputs.tensorProj 0 u := by
  unfold Prop025OInputs.tensorProj
  apply Prop001RseventeenZero.unit_density_eq (zeroSectorIso (𝕜 := ℂ) (E := L2T L))
    (htpow 0 u) (zeroSectorIso_htpow u)
  · exact reducedDensityN_isPositive N 0 (Nat.zero_le N) ψ
  · exact traceIn_reducedDensityN_eq_one N 0 (Nat.zero_le N) _ ψ hψ

#print axioms rank_zero_marginal
end QuantumNLS.TerraMultiRound88Zero
