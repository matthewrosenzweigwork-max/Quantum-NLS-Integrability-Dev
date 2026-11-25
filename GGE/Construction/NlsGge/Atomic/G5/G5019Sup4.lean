import Mathlib
import NlsGge.Atomic.G5.G5001Host
import NlsGge.Atomic.G1.G1085
import NlsGge.Atomic.G1.G1066
import NlsGge.Atomic.G1.G1082Sup5

                                                                                       
                                                                               
                                                                                                                                    
                                                                                                                                  
                                                                                                                              
                                                                      
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
