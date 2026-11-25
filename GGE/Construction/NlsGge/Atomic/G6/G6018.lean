import Mathlib
import NlsGge.Atomic.G6.G6018Sup1Core
import NlsGge.Atomic.G6.G6017
import NlsGge.Atomic.G6.G6013

                                                                                                             
                                                                                                          
                                                                                                 
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6018 (z w : Lib.L2Z)
    (hrad : ∀ n : ℤ, ‖z n‖^2 = ‖w n‖^2)
    (hfin : {n : ℤ | z n ≠ w n}.Finite) :
  (∃ t : ℤ → ℝ, (Function.support t).Finite ∧
    Function.support t ⊆ {n : ℤ | z n ≠ w n} ∧
    ∀ n : ℤ, z n = Complex.exp (-Complex.I * (t n : ℂ)) * w n) ∧
  physicalInverseBirkhoff z ∈ isospectralSet (physicalInverseBirkhoff w) :=
  G6018Aux.core18 G6013.2.2.2.2.2 G6017 z w hrad hfin

end
end NlsGge.GKDefinitionDesign
