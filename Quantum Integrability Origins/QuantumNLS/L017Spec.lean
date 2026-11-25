import QuantumNLS.ResetMoserProcedure
/-! integrator-authored trusted spec for LOCAL-017 thm:reset-moser (review record r39 FULL support): headline statement(s) copied verbatim from ResetMoserProcedure (QuantumNLS.ResetMoser). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open scoped ComplexConjugate Topology ENNReal NNReal
open Filter Set Metric Asymptotics
open scoped Classical
namespace QuantumNLS.L017Spec
open QuantumNLS.ResetMoser
open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoserClamp QuantumNLS.LOCAL017SourceR19
  QuantumNLS.Ext025A4BanachComplexification
variable {S : Hyp} (MD : MoserData S)

set_option maxHeartbeats 8000000 in
theorem reset_moser_printed_flow_spec (P : PrintedHyp) :
    Nonempty (PrintedBounds P) ∧
    ∀ B : PrintedBounds P,
      0 < moserRadius B.radius B.realConstant ∧ moserRadius B.radius B.realConstant ≤ P.R ∧
        ∃ Sm Si : K → K, ∃ C : ℝ,
          MoserData.CorrectsWith P.Ω (moserRadius B.radius B.realConstant) Sm Si C ∧
          MoserFlowSpec P.moserY (moserR0 B.radius B.realConstant) (moserRadius B.radius B.realConstant) Sm Si := by
  exact QuantumNLS.ResetMoser.reset_moser_printed_flow P

end QuantumNLS.L017Spec
#print axioms QuantumNLS.L017Spec.reset_moser_printed_flow_spec
