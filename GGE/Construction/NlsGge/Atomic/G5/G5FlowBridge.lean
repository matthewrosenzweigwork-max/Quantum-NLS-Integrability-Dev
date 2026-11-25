import Mathlib
import NlsGge.Atomic.G1.G1081Host
import NlsGge.Atomic.G1.G1081Sup2

                                                                                      
                                                                                  
                                                                                                                                      
                                                                                                                         
                                                                                                                                            
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def IsSpectralFlow (k : ℤ) (c : ℝ → PhysicalL2) : Prop :=
  ∀ t : ℝ, HasDerivAt (fun s => realSlice (c s))
    (PoissonSpectral38.spectralDiscrimHamField38 (realSlice (c t))
      (muSeq (realSlice (c t)) k)) t

theorem completeGapFlow_isSpectralFlow
    (k : ℤ) (f : ℝ → PhysicalL2 → PhysicalL2)
    (hf : completeGapFlow k f) (u : PhysicalL2) :
  IsSpectralFlow k (fun t : ℝ => f t u) := by
  intro t
  have h := realSlice.hasFDerivAt.comp_hasDerivAt t (hf.2 u t)
  rw [NlsGge.Atomic.G1081Sup2.realSlice_singleGapField, ← muSeq_eq_gkMu38] at h
  exact h

end
end NlsGge.GKDefinitionDesign
