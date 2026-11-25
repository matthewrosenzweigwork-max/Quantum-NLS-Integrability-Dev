import Mathlib
import NlsGge.Atomic.G6.G6024Sup2Core
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompat
import NlsGge.Atomic.KSN.KSN019
import NlsGge.Atomic.KSN.KSN001Sup1

                                                                                                                 
                                                                                                                       
                                                                                                           
                                                                                                                       
                                                                                                                      
                                                                                                                  
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6024 (m : ℕ) (hm : 1 ≤ m) :
  (∀ u : PhysicalSobolev38 (m : ℝ),
    (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ) ∧
    sequenceSobolevEmbed m (birkhoffSobolev m u) =
      physicalBirkhoff (physicalSobolevEmbed m u)) ∧
  AnalyticOnNhd ℝ (birkhoffSobolev m) Set.univ :=
  ⟨fun u => ⟨birkhoffSobolev_mem m u, birkhoffSobolev_coe m u⟩,
    NlsGge.ThirdConsultation.G6024S.birkhoffSobolev_analytic_of m (birkhoffSobolev_mem m) NlsGge.ThirdConsultation.KSN.KSN001Aux.scalarBirkhoff_realSlice
    (KSN019_main m hm).1 (fun x hx => ((KSN019_main m hm).2.1 x hx).1)⟩

end
end NlsGge.GKDefinitionDesign
