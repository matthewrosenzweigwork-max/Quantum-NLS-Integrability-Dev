import Mathlib
import NlsGge.Atomic.M.M005
import NlsGge.Atomic.M.M001
import NlsGge.Atomic.M.M007
import NlsGge.Atomic.M.M014
import NlsGge.ThirdConsultation.M.OddTraceSobolev
import NlsGge.GK38.MolnarMoments
import NlsGge.ThirdConsultation.M.M041Pure

                                                                                           
                                                                                        
                                                                                                                  
                                                                                        
                                                                                        
                                                                                                             
                                                                                                                 
                                                                                                                
                                                                                                                     
                                                                                                                   
                                                                                            
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.M041B
noncomputable section

/-- (B1) The M-005 physical function of u ∈ H¹ is the L² image of its ordinary Sobolev coordinates. -/
theorem carrier_eq (u : NlsGge.ThirdConsultation.M.SobolevR 1) :
    sobolevToL2_38 1 (NlsGge.ThirdConsultation.M.ordinarySobolevCoordinates 1 u) =
      NlsGge.ThirdConsultation.M.physicalOfSobolev u := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply, sobolevToL2_38_fourier]
  unfold NlsGge.ThirdConsultation.M.physicalOfSobolev
  rw [riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier]
  unfold riccatiSobolevJetCoefficientL2Recovery28Second
  rw [pow_zero, one_mul]

/-- Fourier coefficients of the coordinates are those of the physical function. -/
theorem coords_fourier (u : NlsGge.ThirdConsultation.M.SobolevR 1) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from
      NlsGge.ThirdConsultation.M.ordinarySobolevCoordinates 1 u) n =
      physicalFourier (NlsGge.ThirdConsultation.M.physicalOfSobolev u) n := by
  rw [← carrier_eq u, sobolevToL2_38_fourier]

/-- Term identity: 4 J_{n,3} = (2/π) ∫_{gap n} (2x)² v. -/
theorem four_higherAction_three (w : PhysicalL2) (n : ℤ) :
    (4 : ℝ) ^ 1 * NlsGge.ThirdConsultation.M.higherAction w n (2 * 1 + 1) =
      (2 / Real.pi) * ∫ x in (actualGapLowerAllE02_38 w n)..(actualGapUpperAllE02_38 w n),
        (2 * x) ^ (2 * 1) * actualGapHeightE02_38 w x := by
  have h := (NlsGge.ThirdConsultation.M.higher_action_gap_integral w n (2 * 1 + 1)
    (by norm_num)).2.2.2.2
  rw [h]
  simp only [NlsGge.ThirdConsultation.M.periodicMinus, NlsGge.ThirdConsultation.M.periodicPlus,
    NlsGge.ThirdConsultation.M.spectralHeight]
  exact four_moment (actualGapHeightE02_38 w) _ _

/-- (B2) The M-005 signed charge at m = 1 equals the spectral continuous charge. -/
theorem signedCharge_eq_chargeSobolev (u : NlsGge.ThirdConsultation.M.SobolevR 1) :
    NlsGge.ThirdConsultation.M.signedCharge 1 u =
      chargeSobolev38 2 1 (NlsGge.ThirdConsultation.M.ordinarySobolevCoordinates 1 u) := by
  have h1 := NlsGge.ThirdConsultation.M.odd_higher_action_trace_sobolev 1 le_rfl u
  have h2 := NlsGge.GK38.momentSum_eq_charge 1 le_rfl (NlsGge.ThirdConsultation.M.physicalOfSobolev u)
    (NlsGge.ThirdConsultation.M.ordinarySobolevCoordinates 1 u) (coords_fourier u)
  have hfun : (fun n : ℤ => (2 / Real.pi) *
      ∫ x in (actualGapLowerAllE02_38 (NlsGge.ThirdConsultation.M.physicalOfSobolev u) n)..
        (actualGapUpperAllE02_38 (NlsGge.ThirdConsultation.M.physicalOfSobolev u) n),
        (2 * x) ^ (2 * 1) * actualGapHeightE02_38 (NlsGge.ThirdConsultation.M.physicalOfSobolev u) x) =
      fun n : ℤ => (4 : ℝ) ^ 1 *
        NlsGge.ThirdConsultation.M.higherAction (NlsGge.ThirdConsultation.M.physicalOfSobolev u) n (2 * 1 + 1) :=
    funext fun n => (four_higherAction_three _ n).symm
  rw [hfun] at h2
  exact h1.unique h2

end
end NlsGge.ThirdConsultation.M041B
