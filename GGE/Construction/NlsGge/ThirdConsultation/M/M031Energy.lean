import Mathlib
import NlsGge.ThirdConsultation.M.M031Host
import NlsGge.ThirdConsultation.M.M021Host
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.Analysis.FullCoverFourier
import NlsGge.Birkhoff.BirkhoffAPI38

   
                                                                                                                  

                                                                                                                     
                                                                                                        
                                                                                                     
                                                                                                             
                                                                                                                
                                                                       
  

set_option autoImplicit false

noncomputable section

open NlsGge.Pilot NlsGge.GK38 NlsGge.Birkhoff
open scoped ENNReal

namespace NlsGge.ThirdConsultation.M

/-- `H1` coefficient summability of an order-one Sobolev embedding (reflected Fourier convention). -/
theorem sobolevEmbed_one_summable (u : NlsGge.Atomic.Common.PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) *
      ‖reflectedFourierL2 (NlsGge.GKDefinitionDesign.physicalSobolevEmbed 1 u) p‖ ^ 2) := by
  have hmem := (mem_seqSobolev38_iff ((1 : ℕ) : ℝ) _).1
    (carrierCoe38_mem ((1 : ℕ) : ℝ) (NlsGge.Atomic.Common.physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) u))
  unfold SobolevSquareSummable at hmem
  refine hmem.congr (fun p => ?_)
  have hf := NlsGge.GKDefinitionDesign.physicalSobolevEmbed_fourier 1 u p
  unfold fourierSeq38 at hf
  rw [← hf]
  congr 1
  have h0 : (0 : ℝ) ≤ 1 + (p : ℝ) ^ 2 := by positivity
  unfold japaneseBracket
  rw [Nat.cast_one, mul_one]
  change Real.sqrt (1 + (p : ℝ) ^ 2) ^ (2 : ℝ) = 1 + (p : ℝ) ^ 2
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt h0]

theorem sourceH1Weight_sq_le (p : ℤ) :
    sourceH1Weight (-2 * p) ^ 2 ≤ 2 * (1 + 4 * Real.pi ^ 2) * (1 + (p : ℝ) ^ 2) := by
  unfold sourceH1Weight
  have h1 := sq_abs (Real.pi * ((-2 * p : ℤ) : ℝ))
  have h2 := abs_nonneg (Real.pi * ((-2 * p : ℤ) : ℝ))
  set a := |Real.pi * ((-2 * p : ℤ) : ℝ)|
  push_cast at h1
  have hp : (0 : ℝ) ≤ Real.pi ^ 2 * (p : ℝ) ^ 2 := by positivity
  nlinarith [sq_nonneg (a - 1), sq_nonneg (p : ℝ), sq_nonneg Real.pi]

/-- One component: weighted cover-coefficient summability. -/
theorem sourceH1_component_summable (u : PhysicalL2)
    (hu : Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) * ‖reflectedFourierL2 u p‖ ^ 2)) :
    Summable (fun k : ℤ => sourceH1Weight k ^ 2 *
      ‖fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 u) k‖ ^ 2) := by
  have hg : Function.Injective (fun p : ℤ => -2 * p) := by
    intro a b h
    simp only at h
    omega
  have hoff : ∀ k ∉ Set.range (fun p : ℤ => -2 * p),
      sourceH1Weight k ^ 2 * ‖fourierCoeff (NlsGge.Analysis.naturalPhysicalCoverL2 u) k‖ ^ 2 = 0 := by
    intro k hk
    have hodd : k % 2 ≠ 0 := by
      intro h0
      exact hk ⟨-(k / 2), by simp only; omega⟩
    rw [NlsGge.Analysis.naturalPhysicalCoverL2_fourier_odd u k hodd, norm_zero]
    ring
  rw [← hg.summable_iff hoff]
  refine Summable.of_nonneg_of_le (fun p => by simp only [Function.comp_apply]; positivity) (fun p => ?_)
    (hu.mul_left (2 * (1 + 4 * Real.pi ^ 2)))
  simp only [Function.comp_apply]
  have heven : (-2 * p) % 2 = 0 := by omega
  have hdiv : (-2 * p) / 2 = -p := by omega
  rw [NlsGge.Analysis.naturalPhysicalCoverL2_fourier_even_index u _ heven, hdiv]
  have hn : ‖physicalFourier (u : PhysicalCircle → ℂ) (-p)‖ = ‖reflectedFourierL2 u p‖ := by
    rw [reflectedFourierL2_apply]
    unfold reflectedFourier
    rw [norm_neg]
  rw [hn, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (sourceH1Weight_sq_le p) (by positivity)

/-- Pro round 14 (M-031) producer obligation: finite source-H1 coefficient energy on the source carrier. -/
theorem sourceH1_energy_ne_top (φ : KSPS.SobolevC 1) :
    MTwoMode.potentialCoefficientEnergy sourceH1Weight (KSPS.toPotPair φ) ≠ ⊤ := by
  have h1 := sourceH1_component_summable _ (sobolevEmbed_one_summable φ.1)
  have h2 := sourceH1_component_summable _ (sobolevEmbed_one_summable φ.2)
  have hsum : Summable (fun k : ℤ => sourceH1Weight k ^ 2 *
      (‖MTwoMode.potentialCoefficientPair (KSPS.toPotPair φ) true k‖ ^ 2 +
        ‖MTwoMode.potentialCoefficientPair (KSPS.toPotPair φ) false k‖ ^ 2)) := by
    refine (h1.add h2).congr (fun k => ?_)
    simp only [MTwoMode.potentialCoefficientPair, KSPS.toPotPair, ite_true, Bool.false_eq_true, ite_false]
    ring
  unfold MTwoMode.potentialCoefficientEnergy
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

end NlsGge.ThirdConsultation.M

end
