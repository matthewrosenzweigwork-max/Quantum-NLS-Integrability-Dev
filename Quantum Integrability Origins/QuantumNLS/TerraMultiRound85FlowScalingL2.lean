import QuantumNLS.TerraMultiRound85FlowScalingH1
import QuantumNLS.TerraMultiRound85H1Density

/-! Extend the actual H¹ flow scaling identity to every physical L² field. -/
set_option autoImplicit false
noncomputable section
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.H1Bridge
open QuantumNLS.L2Flow QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality
open QuantumNLS.TerraMultiRound85FlowScalingH1 QuantumNLS.TerraMultiRound85H1Density
namespace QuantumNLS.TerraMultiRound85FlowScalingL2
variable {L : ℝ} [Fact (0 < L)]

/-- The actual L² flows satisfy the printed amplitude/coupling covariance. -/
theorem flow_scaling {κ : ℝ} (hκ : 0 ≤ κ) (r : ℝ) (u : HL L) (t : ℝ) :
    flowMap hκ ((r : ℂ) • u) t =
      (r : ℂ) • flowMap (mul_nonneg hκ (sq_nonneg r)) u t := by
  have hscalar : Continuous (fun u : HL L => (r : ℂ) • u) := by fun_prop
  have h1 : Continuous (fun u : HL L => flowMap hκ ((r : ℂ) • u) t) :=
    (continuous_flowMap hκ t).comp hscalar
  have h2 : Continuous (fun u : HL L => (r : ℂ) • flowMap (mul_nonneg hκ (sq_nonneg r)) u t) :=
    hscalar.comp (continuous_flowMap (mul_nonneg hκ (sq_nonneg r)) t)
  have he := Continuous.ext_on (denseRange_emb (L := L)) h1 h2 (by
    rintro _ ⟨g, rfl⟩
    exact flow_scale_H1 hκ r g t)
  exact congrFun he u

#print axioms flow_scaling
end QuantumNLS.TerraMultiRound85FlowScalingL2
