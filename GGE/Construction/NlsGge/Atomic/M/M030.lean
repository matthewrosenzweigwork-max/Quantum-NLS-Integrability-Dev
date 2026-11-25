import Mathlib
import NlsGge.ThirdConsultation.M.M030Roots
import NlsGge.ThirdConsultation.M.M030Bridge
import NlsGge.Atomic.G2.G2046

   
                                                                                                            

                                                                                                                  
                                                                                                                   
                                                                                                                       
                                                                                                                       
              
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation

theorem gap_square_schur_bound
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w) (φ : PotPair)
    (hW : φ ∈ gkW)
    (hφ : MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ)
    (hthreshold : 8 * MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
      NlsGge.Atomic.M.M054.indexWeight n) :
    let P : Set ℝ := {r : ℝ | ∃ z : ℂ,
      ∃ hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n,
        r = ‖MTwoMode.offDiagonal φ n z hz true *
          MTwoMode.offDiagonal φ n z hz false‖}
    P.Nonempty ∧ BddAbove P ∧
    ‖NlsGge.GKDefinitionDesign.gap φ n‖ ^ 2 ≤ 6 * sSup P :=
  gap_square_schur_bound_of_label_roots w hw φ hφ n hthreshold
    (periodic_labels_are_local_roots w hw φ hW hφ n hthreshold)

end NlsGge.ThirdConsultation.M

end
