import Mathlib
import NlsGge.ThirdConsultation.I.RemainderWeight
import NlsGge.Atomic.I.I020
import NlsGge.Birkhoff.S03Measure38b
import NlsGge.Weights.UniformSymbolBound38

                                                                                                                                 
                                                                                                                              
                                                                                                                                              
                                                                                                                   
                                                                                
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Measure NlsGge.Weights NlsGge.SpectralFoundations NlsGge.Sobolev38

namespace NlsGge.ThirdConsultation.I

theorem i021 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalL2,
      SobolevSquareSummable 1 (physicalFourier u) → ‖physFS38 1 u‖ ≤ B →
      Summable (fun n : ℤ => fullWeightRate c.val n * actualGapActionAllE02_38 u n *
        japaneseBracket n ^ (-3 / 2 : ℝ)) →
      (∀ n : ℤ,
        gapRemainderTermE02_38 (weight c.val) u n = remainderSummand38 c.val u n ∧
        |gapRemainderTermE02_38 (weight c.val) u n| ≤
          C * fullWeightRate c.val n * actualGapActionAllE02_38 u n *
            japaneseBracket n ^ (-3 / 2 : ℝ)) ∧
      Summable (fun n : ℤ => |gapRemainderTermE02_38 (weight c.val) u n|) ∧
      remainderForWeight (weight c.val) u = remainder38 c.val u ∧
      |remainderForWeight (weight c.val) u| ≤ C *
        (∑' n : ℤ, fullWeightRate c.val n * actualGapActionAllE02_38 u n *
          japaneseBracket n ^ (-3 / 2 : ℝ)) := by
  have hlower : 0 < lower := c.property.1
  have hle : lower ≤ upper := c.property.2.1
  have hb : ∀ j : ℕ, lower ≤ c.val j := fun j => (c.property.2.2 j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (c.property.2.2 j).2
  obtain ⟨CB, hCB, hsym⟩ := uniformSymbolGap38 lower upper hlower hle (max 1 B) (le_max_left _ _)
  refine ⟨CB, hCB.le, fun u hu hnorm hsum => ?_⟩
  have hW : Continuous (weight c.val) := weight_continuous38 hlower hb hu'
  have hn : ‖physicalSobolevL2 1 u hu‖ ≤ max 1 B := by
    rw [i020_norm_eq u hu]; exact hnorm.trans (le_max_right _ _)
  have e : (-3 / 2 : ℝ) = -(3 / 2) := by norm_num
  have hterm : ∀ n : ℤ, gapRemainderTermE02_38 (weight c.val) u n = remainderSummand38 c.val u n :=
    fun n => (remainderSummand38_eq_gapRemainderTerm c.val hW u n).symm
  have hbd : ∀ n : ℤ, |gapRemainderTermE02_38 (weight c.val) u n| ≤
      CB * fullWeightRate c.val n * actualGapActionAllE02_38 u n *
        japaneseBracket n ^ (-3 / 2 : ℝ) := by
    intro n
    rw [hterm n]
    have h1 := abs_remainderSummand_le38 c.val hW u n
      (CB * fullWeightRate c.val n * japaneseBracket n ^ (-3 / 2 : ℝ))
      (fun l hl => by
        have := (hsym c.val hb hu' u hu hn n l hl).2
        rw [e]; exact this)
    refine h1.trans (le_of_eq ?_)
    ring
  have hsumC : Summable (fun n : ℤ => CB * fullWeightRate c.val n * actualGapActionAllE02_38 u n *
      japaneseBracket n ^ (-3 / 2 : ℝ)) := by
    refine (hsum.mul_left CB).congr fun n => ?_
    ring
  have habs : Summable (fun n : ℤ => |gapRemainderTermE02_38 (weight c.val) u n|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hbd hsumC
  have hrem : remainderForWeight (weight c.val) u = remainder38 c.val u := by
    unfold remainderForWeight remainder38
    exact tsum_congr hterm
  refine ⟨fun n => ⟨hterm n, hbd n⟩, habs, hrem, ?_⟩
  have h2 : |∑' n : ℤ, gapRemainderTermE02_38 (weight c.val) u n| ≤
      ∑' n : ℤ, |gapRemainderTermE02_38 (weight c.val) u n| := by
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun n : ℤ => gapRemainderTermE02_38 (weight c.val) u n)
        (by simpa only [Real.norm_eq_abs] using habs)
  have h3 : ∑' n : ℤ, |gapRemainderTermE02_38 (weight c.val) u n| ≤
      ∑' n : ℤ, CB * (fullWeightRate c.val n * actualGapActionAllE02_38 u n *
        japaneseBracket n ^ (-3 / 2 : ℝ)) :=
    Summable.tsum_le_tsum (fun n => (hbd n).trans (le_of_eq (by ring))) habs
      (hsum.mul_left CB)
  rw [tsum_mul_left] at h3
  exact (h2.trans h3)

end NlsGge.ThirdConsultation.I
