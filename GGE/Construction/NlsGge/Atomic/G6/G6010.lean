import Mathlib
import NlsGge.GK38.Lib.InterpolationHilbertOp
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff
import NlsGge.Atomic.G2.G2040

                                                                                                    
                                                                           
                                                                                                                                                     
                                                                                                                                  
                                                                                                                                           
                                                                                      
                                                                       
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G6010Aux

/-- All actions vanish iff the potential is zero (mass identity, G2-040). -/
theorem actions_zero_iff (u : PhysicalL2) :
    (∀ n : ℤ, actualGapActionAllE02_38 u n = 0) ↔ u = 0 := by
  have hs := G2_040.2 u
  constructor
  · intro h
    have h0 : HasSum (actualGapActionAllE02_38 u) 0 := by
      have : actualGapActionAllE02_38 u = fun _ => 0 := funext h
      rw [this]; exact hasSum_zero
    have := hs.1.unique h0
    have hn : ‖u‖ ^ 2 = 0 := this
    exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 hn)
  · rintro rfl n
    have h1 := (hs.1)
    have h2 : (0 : ℝ) ≤ actualGapActionAllE02_38 (0 : PhysicalL2) n := realActionNonneg38 0 n
    have h3 := (hasSum_zero_iff_of_nonneg (fun m => realActionNonneg38 (0 : PhysicalL2) m)).1
      (by simpa using h1)
    exact congrFun h3 n

end G6010Aux

theorem G6010 :
  realBirkhoffCartesian ⁻¹' ({0} : Set CartesianReal) = {0} ∧
  physicalBirkhoff ⁻¹' ({0} : Set Lib.L2Z) = {0} := by
  refine ⟨?_, ?_⟩
  · ext u
    simp only [mem_preimage, mem_singleton_iff]
    rw [← G6010Aux.actions_zero_iff]
    constructor
    · intro h n
      have ht := congrArg (fun z : CartesianReal => z (true, n)) h
      have hf := congrArg (fun z : CartesianReal => z (false, n)) h
      simp only [realBirkhoffCartesian_true, realBirkhoffCartesian_false] at ht hf
      have := realX_sq_add_realY_sq n u
      have hx : realX n u = 0 := ht
      have hy : realY n u = 0 := hf
      rw [hx, hy] at this
      linarith
    · intro h
      refine lp.ext (funext fun j => ?_)
      obtain ⟨b, n⟩ := j
      have := realX_sq_add_realY_sq n u
      rw [h n] at this
      cases b
      · rw [realBirkhoffCartesian_false]
        exact (show realY n u = 0 by nlinarith [sq_nonneg (realX n u), sq_nonneg (realY n u)])
      · rw [realBirkhoffCartesian_true]
        exact (show realX n u = 0 by nlinarith [sq_nonneg (realX n u), sq_nonneg (realY n u)])
  · ext u
    simp only [mem_preimage, mem_singleton_iff]
    rw [← G6010Aux.actions_zero_iff]
    constructor
    · intro h n
      have ha := sourceFamily.Phi_action u n
      have hn : sourceFamily.Phi u n = 0 := by
        have := congrArg (fun z : Lib.L2Z => z n) h
        simpa [physicalBirkhoff] using this
      rw [hn] at ha
      simpa using ha.symm
    · intro h
      refine lp.ext (funext fun n => ?_)
      have ha := sourceFamily.Phi_action u n
      rw [h n] at ha
      have : ‖sourceFamily.Phi u n‖ = 0 := by simpa using ha
      show sourceFamily.Phi u n = 0
      exact norm_eq_zero.1 this

end
end NlsGge.GKDefinitionDesign
