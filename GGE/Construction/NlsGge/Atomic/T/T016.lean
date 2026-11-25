import NlsGge.Birkhoff.F11Claim38b

                                                                                             
                                                                                                    
                                                                                
                                                                                      
                                                                                             
                                                                                                             

set_option autoImplicit false
open Filter Topology NlsGge.Pilot NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.T

theorem finiteChargeTilt_product_limit
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (J : ℕ) (t : ℕ → ℝ) (ht : TiltAdmissible38 c J t) :
    (∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ n : ℤ, ε ≤ 1 - tiltX38 c J t n ∧
        1 - tiltX38 c J t n ≤ 1) ∧
    (∀ n : ℤ, 0 ≤ tiltX38 c J t n) ∧
    Summable (tiltX38 c J t) ∧
    (∃ D : ℝ, 0 < D ∧
      Tendsto (tiltDet38 c J t) atTop (nhds D) ∧
      ∀ N : ℕ, D ≤ tiltDet38 c J t N ∧
        tiltDet38 c J t N ≤ 1) := by
  obtain ⟨ε, hε0, hε1, hε⟩ := exists_tiltRatio38 c ht
  obtain ⟨D, hD, hT⟩ := tiltDet_tendsto38 ht
  refine ⟨⟨ε, hε0, hε1, fun n => ⟨tiltFactor_ge38 ht hε n, tiltFactor_le38 ht n⟩⟩,
    fun n => tiltX38_nonneg ht n, summable_tiltX38 ht, ⟨D, hD, hT, fun N =>
      ⟨(tiltDet_antitone38 ht).le_of_tendsto hT N, tiltDet_le_one38 ht N⟩⟩⟩

end NlsGge.ThirdConsultation.T
