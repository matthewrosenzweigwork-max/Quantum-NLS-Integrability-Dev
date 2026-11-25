import QuantumNLS.AuditWeightedAssemblyR50a
import QuantumNLS.HierarchyInputR25m

/-! INTERMEDIATE assembly for R-115CAA16. This proves the analytical
substitution directly from accepted scalar moments and the authorized
conditional REG-015 import. It does not claim integrator acceptance or
supply the FINAL named theorem, which must bind accepted R-7B122087. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace QuantumNLS.AuditWeightedBindingR25m
open QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels
open QuantumNLS.EmpiricalRapidity QuantumNLS.BulkResponseActual
open QuantumNLS.BetheCoefficientTransform
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.CommonBethePacket
open QuantumNLS.AuditWeightedProbabilityR49a QuantumNLS.AuditWeightedSeriesR49a
open QuantumNLS.AuditWeightedValuesR50a QuantumNLS.AuditWeightedTightR50a
open QuantumNLS.AuditWeightedSelectionR50a QuantumNLS.AuditWeightedCommonPacketR50a
variable {L κ : ℝ} [Fact (0 < L)] {f : ℝ → ℂ}

/-- R-115CAA16 INTERMEDIATE, with exactly one named missing-predecessor
argument for the entire printed thm:hierarchy. Its analytic conclusion is the
frozen R50a conclusion verbatim. The analytic proof is independent of the
hierarchy, but the required formal theorem argument is retained explicitly.
The source-final named theorem must replace it by the accepted import. -/
theorem audit_weighted_intermediate (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖=1)
    (HierarchyR7B122087Input : QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input
      (L := L) hκ) :
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
        error hκ (smoothL2 hf) p N m ≤ ε) ∧
      ∀ N (ev : MArr N → ℝ), vector (P N) ∈
        (QuantumNLS.BetheSpectralCharges.multiplier (physBasis L hκ N) ev).domain := by
  exact QuantumNLS.AuditWeightedAssemblyR50a.audit_weighted_intermediate hκ hf hu

end QuantumNLS.AuditWeightedBindingR25m
#print QuantumNLS.AuditWeightedBindingR25m.audit_weighted_intermediate
#print axioms QuantumNLS.AuditWeightedBindingR25m.audit_weighted_intermediate
