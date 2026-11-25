                                                                                                                         
                                                                                                 
                                         
import Mathlib
import NlsGge.GK38.PairRealBridgeProbe

                                                                                             
                                                                                                    
                                                                                                                                  
                                                                                                                    

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

