import QuantumNLS.IndependentScalingConversionR42b
/-! integrator-authored trusted spec for R-71F7DDC8 and DEF-021 completion (review record r66 ACCEPT): headline statement(s) copied verbatim from IndependentScalingConversionR42b (QuantumNLS.IndependentScalingConversionR42b). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open MeasureTheory
namespace QuantumNLS.R71FSpec
open QuantumNLS.IndependentScalingConversionR42b
open PhysicalTensor (L2T)
open PeriodFieldR42b Def021ChartR41b HierarchyScaling
variable (L κ : ℝ) [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem independent_scaling_conversion_spec (hκ : 0 < κ) (u : L2T L) :
    Phi L κ u = Phi 1 (κ*L) (period L u) ∧
    Phi L κ u = (Real.sqrt (κ*L))⁻¹ • Phi 1 1 (unitPotential L κ u) := by
  exact QuantumNLS.IndependentScalingConversionR42b.independent_scaling_conversion L κ hκ u

set_option maxHeartbeats 8000000 in
theorem def021_arbitrary_period_formula_spec : PeriodCouplingNormalization Phi := by
  exact QuantumNLS.IndependentScalingConversionR42b.def021_arbitrary_period_formula

/-- integrator pin: the unit potential is literally sqrt(κL) • (period L u). -/
theorem unitPotential_literal (u : L2T L) :
    unitPotential L κ u = Real.sqrt (κ*L) • period L u := rfl

end QuantumNLS.R71FSpec
#print axioms QuantumNLS.R71FSpec.independent_scaling_conversion_spec
#print axioms QuantumNLS.R71FSpec.def021_arbitrary_period_formula_spec
