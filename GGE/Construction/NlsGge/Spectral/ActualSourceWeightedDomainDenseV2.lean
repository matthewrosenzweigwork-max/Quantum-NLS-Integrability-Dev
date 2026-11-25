import NlsGge.Spectral.ActualSourceWeightedDomainTransportBridgeV4
import NlsGge.Spectral.ActualFreeWeightedDomainDenseV4
import NlsGge.Schur.PhysicalSector

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open Set
open TransportBridgeV4

/-- The recovered actual source weighted domain is dense in the source
L² space. This transports the already-proved coordinate-domain density
through the actual source-pair linear isometry equivalence. -/
theorem recoveredActualSourceFreeWeightedDomain_dense (n : ℤ) :
    Dense (recoveredActualSourceFreeWeightedDomain n : Set SourcePairL2) := by
  let e := sourcePairRepr n
  have hd : Dense (freeWeightedDomainPointwise n : Set (SectorSquare n)) :=
    freeWeightedDomainPointwise_dense n
  have hrange : DenseRange (fun y : SectorSquare n => (e.symm y : SourcePairL2)) :=
    e.symm.surjective.denseRange
  have hcontinuous : Continuous (fun y : SectorSquare n => (e.symm y : SourcePairL2)) :=
    e.symm.continuous
  have hmaps : MapsTo (fun y : SectorSquare n => (e.symm y : SourcePairL2))
      (freeWeightedDomainPointwise n : Set (SectorSquare n))
      (recoveredActualSourceFreeWeightedDomain n : Set SourcePairL2) := by
    intro y hy
    change e (e.symm y) ∈ freeWeightedDomainPointwise n
    rw [e.apply_symm_apply]
    exact hy
  exact hrange.dense_of_mapsTo hcontinuous hd hmaps

end NlsGge.Schur

end
