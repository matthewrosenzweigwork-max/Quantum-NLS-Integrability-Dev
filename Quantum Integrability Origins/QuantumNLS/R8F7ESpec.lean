import QuantumNLS.StrongLimitBulk
/-! integrator-authored trusted spec for R-8F7E0394 CC:F03:deterministic (review record r15 FULL ACCEPT): headline statement(s) copied verbatim from StrongLimitBulk (QuantumNLS.StrongLimitBulk). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace QuantumNLS.R8F7ESpec
open QuantumNLS.StrongLimitBulk
open QuantumNLS.BulkResponseRiesz (mu2 isBulkResponse_congr hasFiniteSecondMoment_of_moment)
open QuantumNLS.QuantileForm (uI formEnergy_congr quantile_ae_qm)
open QuantumNLS.QuantileTransport (qm map_qm measurable_qm)
open QuantumNLS.BulkResponseForm (BulkResponseData bulkQuantile IsSmoothQuantilePullback IsFormCore
  IsBulkResponse formDomain L2Unit formEnergy)
open QuantumNLS.StepIntegrals (stepF stepL2)
open QuantumNLS.FiniteResponse (Bop)
open QuantumNLS.GLowerBound (ENint)

set_option maxHeartbeats 8000000 in
theorem strong_limit_bulk_spec (D : BulkResponseData) {F : L2Unit} (hF : D.IsResponse F)
    {N : ℕ → ℕ} (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (q : ∀ n, Fin (N n) → ℝ) (Fv : ∀ n, Fin (N n) → ℝ)
    (hFv : ∀ n, Bop D.L (D.κ / N n) (q n) (Fv n) = q n)
    (hQc : Tendsto (fun n => ‖stepL2 (q n) - Q2 D‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖stepL2 (Fv n) - F‖) atTop (𝓝 0) ∧
    Tendsto (fun n => (ENint (D.κ / N n) (stepF (N n) (q n)) (stepF (N n) (Fv n))).toReal) atTop
      (𝓝 (formEnergy (qm D.μ) F).toReal) := by
  first
  | exact QuantumNLS.StrongLimitBulk.strong_limit_bulk
  | (apply QuantumNLS.StrongLimitBulk.strong_limit_bulk <;> assumption)

end QuantumNLS.R8F7ESpec
#print axioms QuantumNLS.R8F7ESpec.strong_limit_bulk_spec
