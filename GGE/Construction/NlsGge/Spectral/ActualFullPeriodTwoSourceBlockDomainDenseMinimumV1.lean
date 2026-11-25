import NlsGge.Spectral.ActualFullPeriodTwoSourceBlockOperatorV4
import NlsGge.Spectral.ActualSourceWeightedDomainDenseV2

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open TransportBridgeV4

def actualFullPeriodTwoSourceBlockTopologyHomeomorph :
    ActualFullPeriodTwoSourcePair ≃ₜ (Fin 2 → SourcePairL2) :=
  PiLp.homeomorph 2 (fun _ : Fin 2 => SourcePairL2)

/-- Exact set-theoretic form of the two-block domain as the preimage of the
ordinary finite product of its sector domains under PiLp's topology
homeomorphism. -/
theorem actualFullPeriodTwoSourceBlockDomain_eq_homeomorph_preimage_pi :
    (actualFullPeriodTwoSourceBlockDomain : Set ActualFullPeriodTwoSourcePair) =
      actualFullPeriodTwoSourceBlockTopologyHomeomorph ⁻¹'
        Set.pi Set.univ (fun p : Fin 2 =>
          (recoveredActualSourceFreeWeightedDomain (p.val : ℤ) : Set SourcePairL2)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
  change (∀ p : Fin 2,
      x p ∈ recoveredActualSourceFreeWeightedDomain (p.val : ℤ)) ↔
    ∀ p : Fin 2,
      (actualFullPeriodTwoSourceBlockTopologyHomeomorph x) p ∈
        recoveredActualSourceFreeWeightedDomain (p.val : ℤ)
  constructor
  · intro hx p
    have hp : actualFullPeriodTwoSourceBlockTopologyHomeomorph x p = x p := by
      rfl
    simpa only [hp] using hx p
  · intro hx p
    have hp : actualFullPeriodTwoSourceBlockTopologyHomeomorph x p = x p := by
      rfl
    simpa only [hp] using hx p

/-- The finite source-block graph domain is dense, reduced to the exact
homeomorphism-preimage identity and the two existing sector-domain density
theorems. -/
theorem actualFullPeriodTwoSourceBlockDomain_dense_minimum :
    Dense (actualFullPeriodTwoSourceBlockDomain : Set ActualFullPeriodTwoSourcePair) := by
  rw [actualFullPeriodTwoSourceBlockDomain_eq_homeomorph_preimage_pi]
  apply (dense_pi Set.univ fun p _ =>
    recoveredActualSourceFreeWeightedDomain_dense (p.val : ℤ)).preimage
  exact actualFullPeriodTwoSourceBlockTopologyHomeomorph.isOpenMap

end NlsGge.Schur

end
