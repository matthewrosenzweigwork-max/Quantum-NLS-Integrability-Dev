import Mathlib
import NlsGge.Atomic.G4.G4NormalizedHost

                                                                                                                
                                                                               
                                                                                                                           
                                                                                                                     
                                                                                         
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def NormalizedZetaGapBound (V : Set PotPair) (L : ℝ) : Prop :=
  0 ≤ L ∧ V ⊆ sourceBetaW ∧
  ∀ φ ∈ V, ∀ n : ℤ,
    ‖normalizedZeta n φ (tauN φ n) - 1‖ ≤ L * ‖lamPlus φ n - lamMinus φ n‖

end
end NlsGge.GKDefinitionDesign
