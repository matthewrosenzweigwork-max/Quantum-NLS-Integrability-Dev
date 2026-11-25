import Mathlib
import NlsGge.Atomic.KSN.KSN012Host

                                                                                                                             
                                                                                    
                                                                          
                                                                                 
                                                                                                                        
                                                                                                                          
                                                                                                              
                                                                                               
                                                                                                                       
                                                                                                                             
                                                                                                
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

theorem sup4_physicalFourier_star (u : PhysicalL2) (n : ℤ) :
    physicalFourier (⇑(star u)) n = star (physicalFourier (⇑u) (-n)) := by
  unfold physicalFourier fourierCoeff
  rw [Complex.star_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u] with t ht
  rw [ht]
  simp [fourier_neg, Complex.star_def]

theorem sup4_pairPotential_snd_eq_star (x : PairScale 1) (hx : IsRealPair 1 x) :
    (pairPotential 1 (by norm_num) x).2 = star (pairPotential 1 (by norm_num) x).1 := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  change physicalFourierL2 (physicalFourierL2.symm ⟨rawCoefficient 1 x false, rawCoefficient_mem 1 (by norm_num) x false⟩) n =
    physicalFourierL2 (star (physicalFourierL2.symm ⟨rawCoefficient 1 x true, rawCoefficient_mem 1 (by norm_num) x true⟩)) n
  rw [LinearIsometryEquiv.apply_symm_apply, physicalFourierL2_apply, sup4_physicalFourier_star,
    ← physicalFourierL2_apply, LinearIsometryEquiv.apply_symm_apply]
  exact hx n

theorem sup4_pairPotential_eq_realSlice (x : PairScale 1) (hx : IsRealPair 1 x) :
    pairPotential 1 (by norm_num) x = realSlice (pairPotential 1 (by norm_num) x).1 := by
  rw [realSlice_apply]
  exact Prod.ext rfl (sup4_pairPotential_snd_eq_star x hx)

/-- Bridge B4: real pairs lie in the X-006 scalar domain `sourceBetaW`. -/
theorem realPair_mem_sourceBetaW :
    ∀ x : PairScale 1, IsRealPair 1 x → pairPotential 1 (by norm_num) x ∈ sourceBetaW := by
  intro x hx
  rw [sup4_pairPotential_eq_realSlice x hx]
  exact sourceFamily.V_real ⟨_, rfl⟩

end
end NlsGge.ThirdConsultation.KSN
