import QuantumNLS.RootGFullDomain
/-! integrator-authored trusted spec for R-C4F43CA8 thm:root-involution C1 on the closed domain (Terra r161 FULL ACCEPT): headline statement(s) copied verbatim from RootGFullDomain (QuantumNLS.RootGFullDomain). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology Metric
namespace QuantumNLS.RC4FSpecB
open QuantumNLS.RootGFullDomain
open QuantumNLS.RootMeasureComplex QuantumNLS.RootGNeighbourhood QuantumNLS.RootGLocal
  QuantumNLS.PhysicalTensor QuantumNLS.RootFzRadius3 QuantumNLS.RootRelationExtension
  QuantumNLS.RootCauchyHolo QuantumNLS.NormalizedTransfer QuantumNLS.RootSymbolFrechet

set_option maxHeartbeats 8000000 in
theorem G_c1_full_domain_spec (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz4 : 4 * κ ≤ z.im)
    (hzL : Real.log 16 ≤ L * z.im) :
    ∃ V : Set (L2T L), IsOpen V ∧ Metric.sphere (0 : L2T L) 1 ⊆ V ∧
      ContDiffOn ℝ 1
        (fun u : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) z) V := by
  first
  | exact QuantumNLS.RootGFullDomain.G_c1_full_domain
  | (apply QuantumNLS.RootGFullDomain.G_c1_full_domain <;> assumption)

end QuantumNLS.RC4FSpecB
#print axioms QuantumNLS.RC4FSpecB.G_c1_full_domain_spec
