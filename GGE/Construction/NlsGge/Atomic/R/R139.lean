import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Birkhoff.W10Localized38g
import NlsGge.Birkhoff.W10Localized38h
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

theorem r139_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (hFb : ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    0 < ∫ u, chiR38 χ R u ∂((B).muW38 c.val) ∧
    Tendsto (fun N : ℕ =>
        (∫ x, F (physOfE38 c s (projE38 c s N x)) * chiR38 χ R (physOfE38 c s (projE38 c s N x)) *
          fN38 c s N x ∂(fullWeightedSequenceGaussian c s)) /
        ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s)) atTop
      (𝓝 (∫ u, F u ∂((B).locLimitLaw38 c χ R))) :=
  (B).W10_normalized_Es38 O c hs hs' hχ hR F hF hFb

theorem r139_2 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)))
    (hFb : ∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) :
    Tendsto (fun N : ℕ =>
        (∫ x, F (physOfE38 c s (projE38 c s N x)) * chiR38 χ R (physOfE38 c s (projE38 c s N x)) *
          fN38 c s N x ∂(fullWeightedSequenceGaussian c s)) /
        ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s)) atTop
      (𝓝 (∫ u, F u ∂((B).locLimitLaw38 c χ R))) :=
  (B).W10_normalized_Sobolev38 O c hs hs' hχ hR r hr F hF hFb

end NlsGge.ThirdConsultation.R
