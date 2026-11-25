import QuantumNLS.ValuesConcentration
/-! integrator-authored trusted spec for R-0270D1F7 values:prop:concentration (Terra r165 FULL ACCEPT): headline statement(s) copied verbatim from ValuesConcentration (QuantumNLS.ValuesConcentration). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace QuantumNLS.R0270Spec
open QuantumNLS.ValuesConcentration
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.RootMeasureComplex (GN HighHalf)
open QuantumNLS.BetheCoefficientTransform (bornLaw)
open QuantumNLS.RootMeasureConcentration (norm_GN_le)
open QuantumNLS.RootMeasureConcentrationSharp (Csharp Kc_nonneg concentration_sharp)
open QuantumNLS.RootMeasureExistence (cauchy_empirical physBasis_eq cauchy_limiting_measure)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis empiricalProb IsLimitingRapidityMeasure)
open QuantumNLS.CauchyUniqueness (cauchyTransform)
open QuantumNLS.Prop017Bias (Cg born_mean_G)
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem values_concentration_spec {κ K : ℝ} (hκ : 0 < κ) (hκK : κ ≤ K) :
    0 < max (4 * K) (Real.log 16 / L) ∧ 0 < max Csharp (|Cg| * K) ∧
    ∀ (N : ℕ) (hN : 0 < N) (u : L2T L) (hu : ‖u‖ = 1) (μ : ProbabilityMeasure ℝ),
      IsLimitingRapidityMeasure L κ hκ u hu μ →
      ∀ z : ℂ, max (4 * K) (Real.log 16 / L) ≤ z.im →
        (∫ m : MArr N, ‖cauchyTransform (empiricalProb L κ N m : Measure ℝ) z -
            cauchyTransform (μ : Measure ℝ) z‖ ^ 2 ∂(bornMeasure (physBasis L hκ N) u hu) ≤
          max Csharp (|Cg| * K) / (N * z.im ^ 2)) ∧
        ‖(∫ m : MArr N, cauchyTransform (empiricalProb L κ N m : Measure ℝ) z
            ∂(bornMeasure (physBasis L hκ N) u hu)) - cauchyTransform (μ : Measure ℝ) z‖ ≤
          max Csharp (|Cg| * K) / (N * z.im ^ 2) := by
  exact QuantumNLS.ValuesConcentration.values_concentration hκ hκK

end QuantumNLS.R0270Spec
#print axioms QuantumNLS.R0270Spec.values_concentration_spec
