import QuantumNLS.RootNlsInvariance
/-! integrator-authored trusted spec for R-BFCC01E8 thm:root-nls-invariance (terra_review r201 PASS): headline statement(s) copied verbatim from RootNlsInvariance (QuantumNLS.RootNlsInvariance). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set
open QuantumNLS.Sobolev QuantumNLS.LocalWellPosedness QuantumNLS.F04Regularity
  QuantumNLS.RootEnergyVariation
namespace QuantumNLS.RBFCSpec
open QuantumNLS.RootNlsInvariance
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RootNlsInvDisc (m32)
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_nls_invariance_spec {κ : ℝ} (hκ : 0 < κ) (T : ℝ) :
    (∀ (u : ℝ → h04 L 3) (v : ℝ → h04 L 1), IsRegularNLSSolution κ T u v →
      SpectralDataConstant hκ T (fun t => U3 (u t))) ∧
    (∀ (w : ℝ → h04 L 1) (us : ℕ → ℝ → h04 L 3) (vs : ℕ → ℝ → h04 L 1),
      ContinuousOn w (Icc (-T) T) →
      (∀ k, IsRegularNLSSolution κ T (us k) (vs k)) →
      TendstoUniformlyOn (fun k t => m31 (us k t)) w atTop (Icc (-T) T) →
      SpectralDataConstant hκ T (fun t => physical (m10 (w t)))) := by
  exact QuantumNLS.RootNlsInvariance.root_nls_invariance hκ T

end QuantumNLS.RBFCSpec
#print axioms QuantumNLS.RBFCSpec.root_nls_invariance_spec
