import Mathlib
import NlsGge.Atomic.G5.G5001Host
import NlsGge.Atomic.G1.G1085
import NlsGge.Atomic.G1.G1066
import NlsGge.Atomic.G1.G1082Sup5

/- G5-019 SUPPORT 4 `G5019Sup4` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5019Sup4.lean, namespace NlsGge.GKDefinitionDesign.
   `dense_interiorRealDirichletGap`: for every index m, the potentials whose m-th Dirichlet point is strictly interior to its (open)
   gap are dense in PhysicalL2.  Route (Pro audit N3): G1-066 gives v near any point with every gap open; G1-085 gives, inside the
   isospectral compact set of v, a point arbitrarily near v with all open-gap Dirichlet points interior; interiority transfers
   along isospectrality (gap endpoints are isospectral invariants). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem dense_interiorRealDirichletGap (m : ℤ) :
    Dense {w : PhysicalL2 | InteriorRealDirichletGap m w} := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨v, hvU, hv⟩ := NlsGge.Atomic.G1066.G1_066.1.inter_open_nonempty U hU hne
  let U' : Set {y : PhysicalL2 // y ∈ isospectralSet v} := Subtype.val ⁻¹' U
  have hU' : IsOpen U' := hU.preimage continuous_subtype_val
  have hne' : U'.Nonempty := ⟨⟨v, (show isospectral v v from fun z => rfl)⟩, hvU⟩
  obtain ⟨y, hyU, hyD⟩ := (G1_085 v).inter_open_nonempty U' hU' hne'
  obtain ⟨h1, h2⟩ := hyD m (hv m)
  refine ⟨y.1, hyU, ?_⟩
  show actualGapLowerAllE02_38 y.1 m < gkMu y.1 m ∧ gkMu y.1 m < actualGapUpperAllE02_38 y.1 m
  rw [isospectral_gapLower_eq y.2 m, isospectral_gapUpper_eq y.2 m]
  exact ⟨h1, h2⟩

end
end NlsGge.GKDefinitionDesign
