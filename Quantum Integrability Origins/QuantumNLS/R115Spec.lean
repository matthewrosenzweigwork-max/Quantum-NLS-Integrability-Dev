import QuantumNLS.Bind7B115CAA16H02
/-! integrator-authored trusted spec for R-115CAA16 lem:audit-weighted (exact printed): headline statement(s) copied verbatim from Bind7B115CAA16H02 (QuantumNLS.Bind7B115CAA16H02). -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace QuantumNLS.R115Spec
open QuantumNLS.Bind7B115CAA16H02
open QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels
open QuantumNLS.EmpiricalRapidity QuantumNLS.BulkResponseActual
open QuantumNLS.BetheCoefficientTransform
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.CommonBethePacket
open QuantumNLS.AuditWeightedProbabilityR49a QuantumNLS.AuditWeightedSeriesR49a
open QuantumNLS.AuditWeightedValuesR50a QuantumNLS.AuditWeightedTightR50a
open QuantumNLS.AuditWeightedSelectionR50a QuantumNLS.AuditWeightedCommonPacketR50a
variable {L κ : ℝ} [Fact (0 < L)] {f : ℝ → ℂ}

set_option maxHeartbeats 8000000 in
theorem audit_weighted_printed_spec (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖=1) :
    (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu
        {m | ε < error hκ (smoothL2 hf) p N m}) atTop (𝓝 0)) ∧
    (∀ r : ℕ, QuantumNLS.BornConvergence.TendstoInProbability
      (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu)
      (fun N m => QuantumNLS.BetheSpectralCharges.eigenvalue L N (κ/N) r m/(N : ℝ))
      (charge L κ f (r+1)).re) ∧
    ∃ P : (N : ℕ) → Packet (physBasis L hκ N),
      Tendsto (fun N => ‖vector (P N)-productVec L N (smoothL2 hf)‖) atTop (𝓝 0) ∧
      (∀ r ε, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        |QuantumNLS.BetheSpectralCharges.eigenvalue L N (κ/N) r m/(N : ℝ)-(charge L κ f (r+1)).re| ≤ ε) ∧
      (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        error hκ (smoothL2 hf) p N m ≤ ε) := by
  first
  | exact QuantumNLS.Bind7B115CAA16H02.audit_weighted_printed
  | (apply QuantumNLS.Bind7B115CAA16H02.audit_weighted_printed <;> assumption)

end QuantumNLS.R115Spec
#print axioms QuantumNLS.R115Spec.audit_weighted_printed_spec
