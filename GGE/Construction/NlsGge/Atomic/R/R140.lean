import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W11Equivalence38b
import NlsGge.Ramer.RamerFiniteChainRule

                                                                                                              
                                                                                                                 
                                                                           
                                                                                                                       
                                                                                                                        
                                                                                                                   
                                                                                  
                                                                                                             
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r140_main {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (fn : ℕ → α → ℝ) (f : α → ℝ) (hfn : ∀ n, Integrable (fn n) μ) (hf : Integrable f μ)
    (hfn0 : ∀ n x, 0 ≤ fn n x) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hconv : TendstoInMeasure μ fn atTop f) :
    Tendsto (fun n => ∫ x, fn n x ⊓ f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
  NlsGge.Birkhoff.tendsto_integral_inf_W11 μ fn f hfn hf hfn0 hf0 hconv

end NlsGge.ThirdConsultation.R
