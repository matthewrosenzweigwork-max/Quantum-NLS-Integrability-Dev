import QuantumNLS.GlobalCompatFinalR47a
/-! integrator-authored trusted spec for R-CA92819A thm:global-compatibility (review record r62 ACCEPT): headline statement(s) copied verbatim from GlobalCompatFinalR47a (QuantumNLS.GlobalCompatR47a). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open scoped ComplexConjugate Topology
open Set Metric Filter
namespace QuantumNLS.RCA92Spec
open QuantumNLS.GlobalCompatR47a
open PhysicalTensor (L2T)
open D01LocalPrimitive (K)
open Local021 (Setting SymKind Mono)
open RF535Final (Local023Body)
open RootIndexedMasses (masses)
open QuantumNLS.Fourier (fourierL2 modeLp)
open LocalSpectral (pm)
open ResetNormalizationUniqueness (Cphys)
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem global_compatibility_spec (L : ℝ) [Fact (0 < L)] :
    ∃ d CL : ℝ, 0 < d ∧ 0 ≤ CL ∧
      ∃ (Φl : ℝ → L2T L → K) (Ψl : ℝ → K → L2T L),
        Local023Body L d CL Φl Ψl ∧
        (∃ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L), Family d Φl Ψl Φ Ψ) ∧
        ∀ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L),
          Family d Φl Ψl Φ Ψ → Compatibility d CL Φ Ψ := by
  exact QuantumNLS.GlobalCompatR47a.global_compatibility L

end QuantumNLS.RCA92Spec
#print axioms QuantumNLS.RCA92Spec.global_compatibility_spec
