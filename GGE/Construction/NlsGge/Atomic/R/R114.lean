import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W07Probability38d
import NlsGge.Ramer.RamerFiniteChainRule

                                                                                                              
                                                                                                                 
                                                                                              
                                                                                                                      
                                                                                                            
                                                                                  
                                                                                                           
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r114_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs' : s < 3 / 4) (hs1 : s ≤ 1) (x : FullWeightedHilbert c s)
    (ns : ℕ → ℕ) (hns : StrictMono ns) (Jlim : ℝ)
    (hJ : Tendsto (fun k => finiteRamerDensity
      (fun v => v + truncField c s ((B).KW06_38 O c hs1) (ns k) v)
        (headPt c (ns k) (coordE c s x))) atTop (𝓝 Jlim)) :
    Tendsto (fun k => fN38 c s (ns k) x) atTop
      (𝓝 (Real.exp (-(remainder38 c.val (physOfE38 c s x))) * Jlim)) :=
  NlsGge.Birkhoff.BirkhoffInput38.tendsto_fN_of_tendsto_J_W07 B O c hs' hs1 x ns hns Jlim hJ

end NlsGge.ThirdConsultation.R
