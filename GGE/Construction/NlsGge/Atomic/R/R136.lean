import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W10Localized38e
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

theorem r136_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs' : s < 3 / 4) (hs1 : s ≤ 1) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y))) (M : ℝ)
    (hM : ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) (z : ECarrier38 c s) :
    Tendsto (fun N : ℕ => (B).PsiN38 O c hs1 χ R F N (headPt c N (coordE c s z))) atTop
      (𝓝 (F (physOfE38 c s (((B).weightedHomeoE38 O c s).symm z)) *
        chiR38 χ R (physOfE38 c s (((B).weightedHomeoE38 O c s).symm z)) *
        Real.exp (-(remainder38 c.val (physOfE38 c s (((B).weightedHomeoE38 O c s).symm z)))))) :=
  BirkhoffInput38.tendsto_PsiN38 B O c hs' hs1 hχ hR F hF M hM z

end NlsGge.ThirdConsultation.R
