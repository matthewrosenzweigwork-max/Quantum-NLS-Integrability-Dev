import QuantumNLS.AuditGapsFinalS02
/-! integrator-authored trusted spec for R-10EE6421 lem:audit-gaps (final): headline statement(s) copied verbatim from AuditGapsFinalS02 (QuantumNLS.AuditGapsFinalS02). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open Filter Topology MeasureTheory
namespace QuantumNLS.R10ESpec
open QuantumNLS.AuditGapsFinalS02
open QuantumNLS.BetheLabels QuantumNLS.BetheOccupationGauge
open QuantumNLS.TerraMultiRound12Definitions QuantumNLS.Def033CoreR24m
open QuantumNLS.ActualModelTargetR53a (HigherFlows)
open QuantumNLS.Def033HierarchyR24m (Smooth physical)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem audit_gaps_final_spec (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) (r : ℕ) (a b : ℤ)
    (ha : 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 a)
    (hb : 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 b)
    (missing : ∀ N, MArr (N + 1) → ℝ) :
    DifferenceLimit hκ (physical u) hu r a b ((D (L := L) hκ).ω r u) missing := by
  first
  | exact QuantumNLS.AuditGapsFinalS02.audit_gaps_final
  | (apply QuantumNLS.AuditGapsFinalS02.audit_gaps_final <;> assumption)

set_option maxHeartbeats 8000000 in
theorem audit_gaps_final_joint_spec (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    {ι : Type} [Fintype ι] (r : ι → ℕ) (a b : ι → ℤ)
    (ha : ∀ i, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 (a i))
    (hb : ∀ i, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 (b i))
    (missing : ι → ∀ N, MArr (N + 1) → ℝ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => originalBorn hκ (physical u) hu N
      {m | ∃ i, ε < |withMissing L κ (N + 1) (r i) (a i) (b i) (missing i N) m -
        target ((D (L := L) hκ).ω (r i) u) (a i) (b i)|}) atTop (𝓝 0) := by
  first
  | exact QuantumNLS.AuditGapsFinalS02.audit_gaps_final_joint
  | (apply QuantumNLS.AuditGapsFinalS02.audit_gaps_final_joint <;> assumption)

end QuantumNLS.R10ESpec
#print axioms QuantumNLS.R10ESpec.audit_gaps_final_spec
#print axioms QuantumNLS.R10ESpec.audit_gaps_final_joint_spec
