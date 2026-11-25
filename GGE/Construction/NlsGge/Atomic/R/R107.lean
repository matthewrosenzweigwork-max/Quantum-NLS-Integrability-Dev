import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W05FiniteGap38
import NlsGge.Birkhoff.W12Tilt38
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

theorem full_energy_identity_weighted {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (hs : s < 3 / 4)
    (x : ECarrier38 c s) :
    spectralEnergyW38 c.val (physOfE38 c s x) =
      ENNReal.ofReal (remainder38 c.val (physOfE38 c s x)) +
        ∑' n : ℤ, ENNReal.ofReal
          (fullWeightRate c.val n *
            ‖(B).Φ (physOfE38 c s x) n‖ ^ 2) := by
  obtain ⟨hiff, hid⟩ := BirkhoffInput38.energy_identity_W05_38 B c s O hs x
  have hR : 0 ≤ remainder38 c.val (physOfE38 c s x) :=
    (BirkhoffInput38.finiteGap_approximation_W05_38 B c s O hs x isExhaustion_Icc38).2.2.2.2
  have hA0 : ∀ n : ℤ, 0 ≤ fullWeightRate c.val n * ‖(B).Φ (physOfE38 c s x) n‖ ^ 2 :=
    fun n => mul_nonneg (fullWeightRate_pos38 c n).le (sq_nonneg _)
  by_cases hA : Summable (fun n : ℤ => fullWeightRate c.val n * ‖(B).Φ (physOfE38 c s x) n‖ ^ 2)
  · have hfin := hiff.2 hA
    rw [← ENNReal.ofReal_toReal hfin, hid hfin, ← ENNReal.ofReal_tsum_of_nonneg hA0 hA,
      ENNReal.ofReal_add (tsum_nonneg hA0) hR, add_comm]
  · have htop : spectralEnergyW38 c.val (physOfE38 c s x) = ⊤ := by
      by_contra h
      exact hA (hiff.1 h)
    have hsum : (∑' n : ℤ, ENNReal.ofReal
        (fullWeightRate c.val n * ‖(B).Φ (physOfE38 c s x) n‖ ^ 2)) = ⊤ := by
      by_contra h
      apply hA
      have := ENNReal.summable_toReal h
      exact this.congr (fun n => ENNReal.toReal_ofReal (hA0 n))
    rw [htop, hsum, add_top]

end NlsGge.ThirdConsultation.R
