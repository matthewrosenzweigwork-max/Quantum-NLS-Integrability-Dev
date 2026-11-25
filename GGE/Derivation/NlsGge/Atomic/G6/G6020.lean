/- G6-020 PRODUCTION01 (proof development review kit; HELD for landing). Source: proof development/G6020_PROOF01.lean (author proof development),
   byte-identical except this header and the removed top-level  line and trailing rerun comments.
   Target NlsGge/Atomic/G6/G6020.lean. -/
import Mathlib
import NlsGge.GK38.PairRealBridgeProbe

/- G6-020 PROOF01 (proof development, AUTHOR).  Statement `G6020` verbatim from Pro STATEMENTS/G6.md.
   Pro definitions copied verbatim (DEFINITIONS/G1.lean.md lines 34-37): isospectral, isospectralSet
   (namespace NlsGge.GKDefinitionDesign).  Route: isospectralSet u = ⋂ z, {v | discrim (realSlice v) z = discrim (realSlice u) z};
   each set is closed since v ↦ discrim (realSlice v) z is continuous (house continuous_discrim_realSlice_joint). -/

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def isospectral (u v : PhysicalL2) : Prop :=
  ∀ z : ℂ, discrim (realSlice v) z = discrim (realSlice u) z

def isospectralSet (u : PhysicalL2) : Set PhysicalL2 := {v | isospectral u v}

theorem G6020 (u : PhysicalL2) : IsClosed (isospectralSet u) := by
  have hc : ∀ z : ℂ, Continuous (fun v : PhysicalL2 => discrim (realSlice v) z) := fun z =>
    Continuous.comp (g := fun p : PhysicalL2 × ℂ => discrim (realSlice p.1) p.2) (f := fun v : PhysicalL2 => (v, z)) continuous_discrim_realSlice_joint (Continuous.prodMk (continuous_id (X := PhysicalL2)) (continuous_const (y := z)))
  have h : isospectralSet u =
      ⋂ z : ℂ, (fun v : PhysicalL2 => discrim (realSlice v) z) ⁻¹' {discrim (realSlice u) z} := by
    ext v; simp [isospectralSet, isospectral]
  rw [h]
  exact isClosed_iInter (fun z => isClosed_singleton.preimage (hc z))

end
end NlsGge.GKDefinitionDesign

