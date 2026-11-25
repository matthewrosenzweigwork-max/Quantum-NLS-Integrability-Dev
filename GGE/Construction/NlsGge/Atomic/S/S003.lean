                                                                                                                    
                                                                                                                                        
import NlsGge.Schur.ActualPotentialTransposeEntryPrerequisites24

                                                                                                                     
                                                                                                     
                                                                                                                            
                                                                                                 
                                                                                                  
                                                                                                                   
                        
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem potential_hankel_upper_entry
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (m l : Sector n) :
    inner ℂ (parityPairVector n (true, m))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (parityPairVector n (false, l))) =
      physicalFourier u₁ ((m.val + l.val) / 2) :=
  coveredH1ParityPairPotential_upper_entry u₁ u₂ hu₁ hu₂ n m l

theorem potential_hankel_entries
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (b c : Bool) (m l : Sector n) :
    inner ℂ (parityPairVector n (b, m))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (parityPairVector n (c, l))) =
      if b = c then 0 else if b then
        physicalFourier u₁ ((m.val + l.val) / 2) else
        physicalFourier u₂ (-(m.val + l.val) / 2) :=
  actualPotentialTranspose_pair_entry_formula24 u₁ u₂ hu₁ hu₂ n b c m l

theorem potential_hankel_block_transpose
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (b c : Bool) (m l : Sector n) :
    inner ℂ (parityPairVector n (b, m))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (parityPairVector n (c, l))) =
    inner ℂ (parityPairVector n (b, l))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (parityPairVector n (c, m))) := by
  rw [potential_hankel_entries u₁ u₂ hu₁ hu₂ n b c m l,
    potential_hankel_entries u₁ u₂ hu₁ hu₂ n b c l m, add_comm (m.val : ℤ) l.val]

end NlsGge.ThirdConsultation.S
end
