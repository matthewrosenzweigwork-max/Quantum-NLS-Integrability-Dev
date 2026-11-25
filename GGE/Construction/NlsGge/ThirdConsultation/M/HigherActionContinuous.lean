import Mathlib
import NlsGge.Atomic.M.M014
import NlsGge.GK38.EigenvalueCompactnessStrong

                                                                            
                                                                                                                 
                                                                                                                 
                        
                                                                                                         
                                                                                                                    
                                                                                                           
                                                                                                                 
                                                                                                                           
                                                                      
                                                                                        
set_option autoImplicit false
noncomputable section
open MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.M

theorem higherAction_continuous_real
    (n : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    Continuous (fun u : PhysicalL2 => higherAction u n k) := by
  set f : PhysicalL2 → ℝ → ℝ := fun u x => x ^ (k - 1) * actualGapHeightE02_38 u x with hf
  have hjoint : Continuous f.uncurry := by
    show Continuous (fun p : PhysicalL2 × ℝ => p.2 ^ (k - 1) * actualGapHeightE02_38 p.1 p.2)
    exact (continuous_snd.pow (k - 1)).mul NlsGge.GK38.gapHeight_joint_continuous_L2_38
  have hprim : Continuous (fun p : PhysicalL2 × ℝ => ∫ x in (0 : ℝ)..p.2, f p.1 x) :=
    intervalIntegral.continuous_parametric_primitive_of_continuous hjoint
  have he : ∀ u : PhysicalL2, higherAction u n k =
      (2 / Real.pi) * ((∫ x in (0 : ℝ)..actualGapUpperAllE02_38 u n, f u x) -
        ∫ x in (0 : ℝ)..actualGapLowerAllE02_38 u n, f u x) := by
    intro u
    have hi (a b : ℝ) : IntervalIntegrable (f u) volume a b :=
      ((continuous_id.pow (k - 1)).mul (continuous_actualGapHeightE02_38 u)).intervalIntegrable a b
    rw [(higher_action_gap_integral u n k hk).2.2.2.2,
      intervalIntegral.integral_interval_sub_left (hi 0 _) (hi 0 _)]
    rfl
  have hl := (NlsGge.GK38.gapEndpoints_L2_continuous38 n).1
  have hu := (NlsGge.GK38.gapEndpoints_L2_continuous38 n).2
  have huP := hprim.comp (continuous_id.prodMk hu)
  have hlP := hprim.comp (continuous_id.prodMk hl)
  have hc := ((huP.sub hlP).const_mul (2 / Real.pi))
  refine hc.congr (fun u => ?_)
  rw [he u]
  rfl

end NlsGge.ThirdConsultation.M
