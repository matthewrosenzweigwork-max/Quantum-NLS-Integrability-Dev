import Mathlib
import NlsGge.Atomic.G6.G6016Host
import NlsGge.Atomic.G6.G6017Sup1Core
import NlsGge.Atomic.G6.G6016

                                                                                                             
                                                                                                                       
                                                                                                                  
                                                                                        
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6017 (u : PhysicalL2) (n : ℤ) (t : ℝ) :
  let v := physicalInverseBirkhoff (rotateOneCoordinate n t (physicalBirkhoff u))
  (∀ lam : ℂ, discrim (realSlice v) lam = discrim (realSlice u) lam) ∧
  v ∈ isospectralSet u :=
  G6017Aux.core17 G6016 u n t

end
end NlsGge.GKDefinitionDesign
