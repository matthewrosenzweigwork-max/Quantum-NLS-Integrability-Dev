import QuantumNLS.RootMeasureContinuity
import QuantumNLS.Prop025OInputs
import QuantumNLS.Prop001RthirteenDerivative

/-! Uniform trace-norm continuity of the physical tensor projector, with
explicit rank dependence and valid also for rank zero. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound88Tensor
open TensorCarrier PhysicalTensor TraceClass
variable {L : ℝ} [Fact (0 < L)]

theorem tensor_projector_lipschitz (k : ℕ) (u v : L2T L)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    traceNorm (Prop025OInputs.tensorProj k u - Prop025OInputs.tensorProj k v) ≤
      ENNReal.ofReal (2 * (k : ℝ) * ‖u - v‖) := by
  let x : HilbertTensorPower ℂ (L2T L) k := htpow k u
  let y : HilbertTensorPower ℂ (L2T L) k := htpow k v
  have hx : ‖x‖ = 1 := by simp [x, norm_htpow, hu]
  have hy : ‖y‖ = 1 := by simp [y, norm_htpow, hv]
  have hd : ‖x - y‖ ≤ (k : ℝ) * ‖u - v‖ :=
    RootMeasureContinuity.norm_htpow_sub_le k u v hu.le hv.le
  have h := Prop001RthirteenDerivative.traceNorm_rankOne_difference x x y y
  change traceNorm (InnerProductSpace.rankOne ℂ x x - InnerProductSpace.rankOne ℂ y y) ≤ _
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hx, hy]
  linarith

#print axioms tensor_projector_lipschitz
end QuantumNLS.TerraMultiRound88Tensor
