import QuantumNLS.Prop001RtwentyTheorem
/-! integrator-authored trusted spec for PROP-001 (terra_review r181 FULL correspondence PASS): the headline
statement copied verbatim from Prop001RtwentyTheorem (namespace QuantumNLS.Prop001RtwentyTheorem). The statement type
is the author structure Prop001RtwentyAssembly.BoundedPropagation H, whose fields Terra r181 checked against the
printed propagation clauses (including the signed-schedule rate with printed constants). -/
set_option autoImplicit false
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
namespace QuantumNLS.P001Spec
open TraceClass TensorCarrier Prop001 Prop001RthirteenSeries Prop001RseventeenContinuity
  Prop001RtwentyIteration Prop001RseventeenVolterra Prop001RtwentyAssembly Prop001RtwentyFlow
  Prop001RtwentyBudget Prop001RtwentySchedule Prop001RtwentySplit
  Prop001RtwentyScheduleRate Prop001RtwentyGlobal Prop001RtwentyForward
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem PROP001_spec : BoundedPropagation H :=
  QuantumNLS.Prop001RtwentyTheorem.PROP001

end QuantumNLS.P001Spec
#print axioms QuantumNLS.P001Spec.PROP001_spec
