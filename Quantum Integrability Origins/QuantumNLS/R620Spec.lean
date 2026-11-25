import QuantumNLS.Round10ScalarReconstructionBatch
/-! integrator-authored trusted spec for R-620D5517 lem:audit-scalar-period (Terra r169 FULL ACCEPT): headline statement(s) copied verbatim from Round10ScalarReconstructionBatch (QuantumNLS.RootScalarPeriodR10). -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Topology Complex
namespace QuantumNLS.R620Spec
open QuantumNLS.RootScalarPeriodR10
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootCauchyJointR9 (Regular)
open RootMassInvolutionR8 (mass)
open RootScalarPeriodR8 (cut center radius)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem audit_scalar_period_spec (hκ : 0 < κ) (u : L2T L) (F : Finset ℤ) :
    ∃ U : Set (L2T L), IsOpen U ∧ u ∈ U ∧ ∀ n ∈ F,
      0 < radius hκ u n ∧
      (∀ v ∈ U, ∀ z ∈ Metric.sphere (center hκ u n : ℂ) (radius hκ u n),
        lambda hκ u z (symbol κ v z) = exponent hκ v z) ∧
      (∀ v ∈ U, leadingPeriod hκ u n v = mass hκ n v) ∧
      (∀ v ∈ U, AnalyticAt ℝ (leadingPeriod hκ u n) v) ∧
      (∀ v ∈ U, fderiv ℝ (leadingPeriod hκ u n) v = fderiv ℝ (mass hκ n) v) ∧
      (∀ v ∈ U, ∀ h : L2T L, fderiv ℝ (leadingPeriod hκ u n) v h =
        fderiv ℝ (mass hκ n) v h) := by
  exact QuantumNLS.RootScalarPeriodR10.audit_scalar_period hκ u F

end QuantumNLS.R620Spec
#print axioms QuantumNLS.R620Spec.audit_scalar_period_spec
