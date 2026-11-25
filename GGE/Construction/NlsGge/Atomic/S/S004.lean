import NlsGge.Schur.SourcePhysicalFreeResolventRealizationV1

                                                                                                                                                                                                                                            
                                                                                                                          
                                                                                                         
                                                                                  
                                                                                
                                                                                                                            
set_option autoImplicit false
noncomputable section
open NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem complementaryResolvent_mem_domain
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (x : SectorSquare n) :
    freeResolventSquare n z hz x ∈ freeWeightedDomainPointwise n :=
  freeResolventSquare_mem_freeWeightedDomain n z hz x

theorem complementaryResolvent_right_inverse
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (x : SectorSquare n) :
    freeShiftedCoordinateDirac n z
      ⟨freeResolventSquare n z hz x,
        freeResolventSquare_mem_freeWeightedDomain n z hz x⟩ =
      complementarySquare n x :=
  freeShiftedCoordinateDirac_right_inverse_complement n z hz x

theorem complementaryResolvent_left_inverse
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (x : freeWeightedDomainPointwise n) :
    freeResolventSquare n z hz
      (freeShiftedCoordinateDirac n z x) =
      complementarySquare n x.val :=
  freeShiftedCoordinateDirac_left_inverse_complement n z hz x

theorem complementaryResolvent_coefficient_bound
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (m : Sector n) (hm : m ≠ resonantIndex n) :
    ‖freeResolventCoeff n z m‖ ≤
      1 / |(m.val : ℝ) - (n : ℝ)| :=
  freeResolventCoeff_bound n z hz m hm

end NlsGge.ThirdConsultation.S
end
