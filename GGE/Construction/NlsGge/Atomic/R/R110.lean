import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.ThirdConsultation.R.R110Host

                                                                                                  
                                                                                                                    
                                                                                                         
                                                                                                                 
                                                                                                                
                                                                                                                     
                                                                                                                  
                                                                                                          
                                                                                                                
                                                                                                                 
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem actual_density_pushforward {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    let hs1 : s ≤ 1 := by linarith
    (∀ x : ECarrier38 c s, 0 < actualRamerDensity c s hs hs1 x) ∧
    Integrable (actualRamerDensity c s hs hs1) (fullWeightedSequenceGaussian c s) ∧
    (∫ x : ECarrier38 c s, actualRamerDensity c s hs hs1 x
      ∂(fullWeightedSequenceGaussian c s)) = (B).ZW38 c.val ∧
    (B).muW38 c.val = ENNReal.ofReal (1 / (B).ZW38 c.val) •
      ((fullWeightedSequenceGaussian c s).withDensity
        (fun x : ECarrier38 c s => ENNReal.ofReal (actualRamerDensity c s hs hs1 x))).map
          (physFW06_38 c s) := by
  intro hs1
  obtain ⟨-, hmap, hpos, hint, -⟩ := Classical.choose_spec
    (NlsGge.Birkhoff.ramer_W06_38 PDE.actualBirkhoffInput38 PDE.actualOneSmoothingInput38 c s hs hs1)
  obtain ⟨h1, h2, h3, h4, -⟩ := NlsGge.Birkhoff.density_W06_38 PDE.actualBirkhoffInput38 c s
    PDE.actualOneSmoothingInput38 hs hs' _ hmap hint hpos
  exact ⟨h1, h2, h3, h4⟩

end NlsGge.ThirdConsultation.R
