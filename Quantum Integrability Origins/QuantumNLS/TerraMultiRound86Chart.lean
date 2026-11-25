import QuantumNLS.REF88Final
import QuantumNLS.GlobalCompatFinalR47a

/-! The accepted physical-dynamics theorem applies to every chart in the
existing compatibility family. This constructs exactly its printed chart
hypotheses from the global extension and compatibility statements. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
namespace QuantumNLS.TerraMultiRound86Chart
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.GlobalCompatR47a
open QuantumNLS.REF88PrintedChartLocal
variable {L : ℝ} [Fact (0 < L)] {κ d CL : ℝ} {hκ : 0 < κ}
variable {Φl : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψl : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}
variable {Φ : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψ : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}
theorem chart_of_extension (h : Extension κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ))
    (hc : Compatibility d CL Φ Ψ) : PrintedChartLocal hκ (Φ κ) := by
  obtain ⟨-, hD, -, hreal, -⟩ := hc.1 κ hκ
  refine ⟨h.strong, h.analytic, h.moduli, fun v => ?_, Filter.Eventually.of_forall hreal⟩
  exact congrArg (fun A : L2T L →L[ℝ] QuantumNLS.D01LocalPrimitive.K => A v) hD
#print axioms chart_of_extension
end QuantumNLS.TerraMultiRound86Chart
