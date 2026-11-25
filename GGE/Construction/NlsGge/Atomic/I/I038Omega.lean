import Mathlib
import NlsGge.Atomic.I.I038Pathwise
import NlsGge.Atomic.I.I038Smooth
import NlsGge.Atomic.I.I038Weight
import NlsGge.ThirdConsultation.I.LimitLaws

                                                                                                                     
                                                                                                 
                                  
                                                                                                                
                                                                                                                      
                                                                                                                    
                                            
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.ThirdConsultation.I NlsGge.Atomic.I037

namespace NlsGge.ThirdConsultation.I038O

theorem omega_remainder_of (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (p : ℝ) (hp : 2 < p) (c : BoundedCoefficients 1 2) :
    ∀ z ∈ {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => factorialPowerWeight p c.val (2 * Real.pi * (n : ℝ)) * ‖z n‖ ^ 2 *
        japaneseBracket n ^ (2 / p - 2))},
      Summable (fun n : ℤ =>
        |gapRemainderTermE02_38 (factorialPowerWeight p c.val) (physicalOfSequence z) n|) ∧
      sequenceRemainder (factorialPowerWeight p c.val) z =
        remainderForWeight (factorialPowerWeight p c.val) (physicalOfSequence z) ∧
      0 ≤ remainderForWeight (factorialPowerWeight p c.val) (physicalOfSequence z) := by
  intro z hz
  have hc : ∀ j, 1 ≤ c.val j ∧ c.val j ≤ 2 := c.property.2.2
  have hp1 : 1 ≤ p := by linarith
  set w : ℤ → ℝ := fun n => factorialPowerWeight p c.val (2 * Real.pi * (n : ℝ)) *
    japaneseBracket n ^ (2 / p - 2) with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n =>
    mul_nonneg (by linarith [weight_ge_one hp1 hc (2 * Real.pi * (n : ℝ))])
      (Real.rpow_nonneg (by unfold japaneseBracket; positivity) _)
  have hgap : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalL2,
      SobolevSquareSummable 1 (physicalFourier u) → ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
        |gapRemainderTermE02_38 (factorialPowerWeight p c.val) u n| ≤
          C * w n * actualGapActionAllE02_38 u n := by
    intro B hB0
    obtain ⟨C, hC, h⟩ := NlsGge.ThirdConsultation.I038W.gap_conjunct p hp c B hB0
    refine ⟨C, hC, fun u hu hBu n => (h u hu hBu n).trans (le_of_eq ?_)⟩
    simp only [hw]; ring
  have hz1 : z ∈ seqSobolev38 ((1 : ℕ) : ℝ) := (mem_seqSobolev38_iff _ _).2 (hz.1 1)
  have hzs : Summable (fun n : ℤ => w n * ‖z n‖ ^ 2) := hz.2.congr fun n => by simp only [hw]; ring
  obtain ⟨h1, -, -, h4⟩ := NlsGge.ThirdConsultation.I038P.pathwise Bk hB _
    (NlsGge.ThirdConsultation.I038S.contDiff_weight hp1 hc)
    (NlsGge.ThirdConsultation.I038S.convexOn_weight hp1 hc) w hw0 hgap z hz1 hzs stdExh38
    isExhaustion_stdExh38
  refine ⟨h1, ?_, h4⟩
  unfold sequenceRemainder
  exact max_eq_right h4

end NlsGge.ThirdConsultation.I038O
