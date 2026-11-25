import Mathlib
import NlsGge.Atomic.G6.G6029Host
import NlsGge.Atomic.G6.G6029Core
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6023
import NlsGge.Atomic.G2.G2030

                                                                                                                 
                                                                                                                      
                                                                                                                    
                                                                                                    
                                                                                                                       
                                                                                                       
                                   
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace
open NlsGge.ThirdConsultation (finiteGap)

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6029 (u : PhysicalL2) :
  ((Function.support (physicalBirkhoff u : ℤ → ℂ)).Finite ↔ finiteGap u) ∧
  (finiteGap u → ∀ m : ℕ, fourierSeq38 u ∈ seqSobolev38 (m : ℝ)) ∧
  (∀ N : ℕ, finiteGap (finiteGapTruncation N u) ∧
    ∀ m : ℕ, fourierSeq38 (finiteGapTruncation N u) ∈ seqSobolev38 (m : ℝ)) :=
  G6029Aux.G6029_of (fun u n => sourceFamily.Phi_action u n) G2_030 G6023 G6013.2.2.2.2.2 u

end
end NlsGge.GKDefinitionDesign
