import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W07Probability38e
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

                                                                                                  
                                                                                                                    
                                                                                                                    
                                                                                                                   
                                                                                                                    
                                                                                                                       
                                                                                                                   
                                                                                                                       
                                                                                                                 
                                                                                                                                
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r116_main {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (f : ℕ → α → ℝ) (g : α → ℝ) (hf : ∀ n, Measurable (f n))
    (hconv : TendstoInMeasure μ f atTop g) (Zn : ℕ → ℝ)
    (hZn : ∀ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂μ = ENNReal.ofReal (Zn n)) {Z : ℝ} (hZ : 0 < Z)
    (hg : ∫⁻ x, ENNReal.ofReal (g x) ∂μ = ENNReal.ofReal Z) :
    ∀ a : ℝ, a < Z → ∀ᶠ n in atTop, a < Zn n :=
  NlsGge.Birkhoff.fatou_liminf_W07 f g hf hconv Zn hZn hZ hg

end NlsGge.ThirdConsultation.R
