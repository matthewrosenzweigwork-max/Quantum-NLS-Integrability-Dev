import Mathlib
import NlsGge.Atomic.X.X009BridgeCore
import NlsGge.Atomic.F.F010Host
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing

                                                                                                                  
                                                                                         
                                                                                                                 
                                                                                                                  
                                
                                                                                                                     
                                                                                                                         
                                                                                                                           
                                                                                                         
                                                                               
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core NlsGge.AblowitzLadik

namespace NlsGge.Atomic.X009.X009Aux

theorem actual_TinvC_eq :
    NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.TinvC (2 - 1) =
      NlsGge.ThirdConsultation.PDE.actualTinvC38 (2 - 1) :=
  (congrArg (fun T : BirkhoffTop38 => T.TinvC (2 - 1))
    NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38_top).trans
    (NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38_TinvC (2 - 1))

theorem inverseOnSequence_eq (z : ℤ → ℂ) :
    NlsGge.ThirdConsultation.F.inverseOnSequence 2 z =
      ofCarrier38 _ (reflC38 _ (NlsGge.ThirdConsultation.PDE.actualTinvC38 (2 - 1)
        (toCarrier38 _ (gaussianRealization38 2 z)))) := rfl

theorem ae_phiInv_eq {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) :
    NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.PhiInvX38 2
      =ᵐ[gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)] NlsGge.ThirdConsultation.F.inverseOnSequence 2 :=
  ae_phiInv_eq_of NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
    (NlsGge.ThirdConsultation.PDE.actualTinvC38 (2 - 1)) actual_TinvC_eq
    (NlsGge.ThirdConsultation.F.inverseOnSequence 2) inverseOnSequence_eq h0 h1 h2

theorem finiteNormalizer_eq_ZM {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) :
    NlsGge.ThirdConsultation.F.finiteNormalizer 2 (alQ4Beta38 β₀ β₁ β₂) =
      ZM38 NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38 2 (alQ4Beta38 β₀ β₁ β₂) := by
  unfold NlsGge.ThirdConsultation.F.finiteNormalizer NlsGge.ThirdConsultation.F.finiteDensity
  exact normalizer_eq_of _ _ _ (ae_phiInv_eq h0 h1 h2)

theorem finiteGapLaw_eq_muM {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) :
    NlsGge.ThirdConsultation.F.finiteGapLaw 2 (alQ4Beta38 β₀ β₁ β₂) =
      muM38 NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38 2 (alQ4Beta38 β₀ β₁ β₂) := by
  have hZ : 0 < ZM38 NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38 2 (alQ4Beta38 β₀ β₁ β₂) := by
    rw [(L06_08b_38 NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
      NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38 h0 h1 h2 0).2.2.1]
    exact alQ4Z2_pos38 h0 h1.le h2
  unfold NlsGge.ThirdConsultation.F.finiteGapLaw NlsGge.ThirdConsultation.F.finiteNormalizer
    NlsGge.ThirdConsultation.F.finiteDensity
  exact law_eq_of _ _ _ (ae_phiInv_eq h0 h1 h2) hZ

end NlsGge.Atomic.X009.X009Aux
