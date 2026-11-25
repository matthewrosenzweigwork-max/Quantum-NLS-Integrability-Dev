import QuantumNLS.ValuesTail
/-! integrator-authored trusted spec for R-CB4CC6EE values:lem:tail (review record r41 PASS): headline statement(s) copied verbatim from ValuesTail (QuantumNLS.ValuesTail). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.RCB4Spec
open QuantumNLS.ValuesTail
open QuantumNLS.ClassicalCharges QuantumNLS.CauchyUniqueness QuantumNLS.FullMass
open QuantumNLS.SmoothScalarMomentsAsymptotic QuantumNLS.SmoothScalarMomentsCauchy
open QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.ValuesTailMarkov (filterF tail_le_two_pow_mul_filter integral_filter_le filterF_nonneg filterF_le_one)
open QuantumNLS.ValuesTailBias (empMeas integrable_of_bdd born_filter_bias)
open QuantumNLS.ValuesTailIdentify (limit_eq_Mmeas integrable_moment_of_limit)
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem values_tail_spec {κ : ℝ} (hκ : 0 < κ) (p : ℕ) (hp : 1 ≤ p) :
    ∃ Cp : ℝ, ∀ (f : ℝ → ℂ) (hf : SmoothPeriodic L f) (hu : ‖smoothL2 hf‖ = 1),
      ∃ Cpf : ℝ, ∀ μ : ProbabilityMeasure ℝ,
        QuantumNLS.BulkResponseActual.IsLimitingRapidityMeasure L κ hκ (smoothL2 hf) hu μ →
        ∀ (N : ℕ) (hN : 0 < N) (R : ℝ), 2 * max (4 * κ) (Real.log 16 / L) ≤ R →
          (∫ m : QuantumNLS.BetheLabels.MArr N, (empMeas L κ N m).real {t : ℝ | R < |t|}
              ∂(QuantumNLS.EmpiricalRapidity.bornMeasure
                  (QuantumNLS.BulkResponseActual.physBasis L hκ N) (smoothL2 hf) hu))
            ≤ Cpf / R ^ (2 * p) + Cp / (N * R) := by
  exact QuantumNLS.ValuesTail.values_tail hκ p hp

end QuantumNLS.RCB4Spec
#print axioms QuantumNLS.RCB4Spec.values_tail_spec
