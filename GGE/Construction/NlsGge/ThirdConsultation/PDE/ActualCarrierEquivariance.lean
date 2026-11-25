import NlsGge.Birkhoff.S01Equivariance38c
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization

                                                                           
                                                                          
                                                                                   

set_option autoImplicit false
noncomputable section
open NlsGge.Sobolev38 NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.PDE

/-- Direct specialization of the completed h0 equivariance theorem to the
actual input, its actual analytic realization, and its actual canonical realization. -/
theorem actual_T_rotation_carrier_zero (theta : ℝ)
    (x : SobolevCarrier38 ((0 : ℕ) : ℝ)) :
    actualBirkhoffInput38.TC 0 (rotC38 ((0 : ℕ) : ℝ) theta x) =
      rotC38 ((0 : ℕ) : ℝ) theta (actualBirkhoffInput38.TC 0 x) := by
  change actualBirkhoffTop38.TC 0 (rotC38 ((0 : ℕ) : ℝ) theta x) =
    rotC38 ((0 : ℕ) : ℝ) theta (actualBirkhoffTop38.TC 0 x)
  exact BirkhoffTop38.rot_T_commute_carrier38 actualBirkhoffTop38
    (actualBirkhoffAnalytic38.mono (Set.subset_univ _))
    actualBirkhoffCanonical38 theta x

/-- The SAME actual T commutes with every rotation on each completed hm carrier. -/
theorem actual_T_rotation_carrier (m : ℕ) (theta : ℝ)
    (x : SobolevCarrier38 (m : ℝ)) :
    actualBirkhoffInput38.TC m (rotC38 (m : ℝ) theta x) =
      rotC38 (m : ℝ) theta (actualBirkhoffInput38.TC m x) := by
  change actualBirkhoffTop38.TC m (rotC38 (m : ℝ) theta x) =
    rotC38 (m : ℝ) theta (actualBirkhoffTop38.TC m x)
  apply carrierExt38
  simp only [BirkhoffTop38.TC_coe, rotC38_coe]
  exact BirkhoffTop38.T_rotSeq38 actualBirkhoffTop38
    (actualBirkhoffAnalytic38.mono (Set.subset_univ _))
    actualBirkhoffCanonical38 (carrierCoe38 (m : ℝ) x)
    (seqSobolev38_natCast_mono (carrierCoe38_mem (m : ℝ) x)) theta

/-- The actual inverse commutes with every rotation on each completed hm carrier. -/
theorem actual_Tinv_rotation_carrier (m : ℕ) (theta : ℝ)
    (z : SobolevCarrier38 (m : ℝ)) :
    actualBirkhoffInput38.TinvC m (rotC38 (m : ℝ) theta z) =
      rotC38 (m : ℝ) theta (actualBirkhoffInput38.TinvC m z) := by
  change actualBirkhoffTop38.TinvC m (rotC38 (m : ℝ) theta z) =
    rotC38 (m : ℝ) theta (actualBirkhoffTop38.TinvC m z)
  apply carrierExt38
  simp only [BirkhoffTop38.TinvC_coe, rotC38_coe]
  exact BirkhoffTop38.Tinv_rotSeq38 actualBirkhoffTop38
    (actualBirkhoffAnalytic38.mono (Set.subset_univ _))
    actualBirkhoffCanonical38 (carrierCoe38 (m : ℝ) z)
    (seqSobolev38_natCast_mono (carrierCoe38_mem (m : ℝ) z)) theta

end NlsGge.ThirdConsultation.PDE
