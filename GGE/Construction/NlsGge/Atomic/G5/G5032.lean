import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5031
import NlsGge.Atomic.G5.G5032Sup1
import NlsGge.Atomic.G4.G4040

                                                                        
                                                                           
                                                                                                                          
                                                                                                     
                                                                                                    
                                         
                                                                    
                                                                                             
                                                                                                                                  
                                                                                                                                  
                                                                                       
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5032 (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0) :
  ∃ ν : ℤ → ℝ, Function.Injective ν ∧
    (∀ k : ℤ, ν k ∈ Set.Icc (actualGapLowerAllE02_38 u k)
      (actualGapUpperAllE02_38 u k) ∧
      doubleAngleDiscriminantBracket m n (realSlice u) (ν k : ℂ) = 0) ∧
    Memℓp (fun k : ℤ => ν k - (k : ℝ) * Real.pi) 2 :=
  G5032Sup1.core32 (fun j v => ⟨(G4040 v j).1, (G4040 v j).2.1⟩) u m n
    (fun k => (G5031 u m n k hm hn).2)

end
end NlsGge.GKDefinitionDesign
