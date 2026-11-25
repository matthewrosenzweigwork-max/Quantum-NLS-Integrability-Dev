import Mathlib
import NlsGge.ThirdConsultation.M.M035Host
import NlsGge.Atomic.M.M001
import NlsGge.Atomic.M.M054
import NlsGge.Spectral.ActualActionSumE02_38
import NlsGge.Birkhoff.S03Measure38b
import NlsGge.ThirdConsultation.M.Round5b
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore
import NlsGge.Atomic.M.M018Tails

                                                                                                                  
                                                                                  
                                                                                                                 
                                                                                                                         
                                                                                                          
                                                                                                                    
                                                                                                               
                                                                                                                
                                                                         
                                                                                                              
                               
set_option autoImplicit false
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.GKDefinitionDesign NlsGge.Birkhoff
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.M035C

open NlsGge.ThirdConsultation.M

theorem H1Norm_nonneg_src (u : SobolevR 1) : 0 ≤ MTwoMode.H1Norm u := by
  unfold MTwoMode.H1Norm; exact Real.sqrt_nonneg _

theorem low_weight_le (m : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (n : ℤ)
    (hn : n = 0 ∨ NlsGge.Atomic.M.M054.indexWeight n < 8 * Q ^ 2) :
    molnarWeight m n ^ 2 ≤ (1 + 16 * Real.pi) ^ (2 * m) * (1 + Q) ^ (4 * m) := by
  have hpi := Real.pi_pos
  have hbase : 1 + |2 * Real.pi * (n : ℝ)| ≤ (1 + 16 * Real.pi) * (1 + Q) ^ 2 := by
    rcases hn with h0 | hlow
    · subst h0; simp; nlinarith [sq_nonneg Q]
    · unfold NlsGge.Atomic.M.M054.indexWeight at hlow
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      nlinarith [abs_nonneg (n : ℝ), sq_nonneg Q, mul_nonneg hpi.le (abs_nonneg (n : ℝ))]
  unfold molnarWeight
  calc ((1 + |2 * Real.pi * (n : ℝ)|) ^ m) ^ 2 = (1 + |2 * Real.pi * (n : ℝ)|) ^ (2 * m) := by
        rw [← pow_mul, Nat.mul_comm]
    _ ≤ ((1 + 16 * Real.pi) * (1 + Q) ^ 2) ^ (2 * m) :=
        pow_le_pow_left₀ (by positivity) hbase _
    _ = (1 + 16 * Real.pi) ^ (2 * m) * (1 + Q) ^ (4 * m) := by
        rw [mul_pow, ← pow_mul]; ring_nf

theorem forward_core
    (hcomp : ∀ (u : SobolevR 1) (n : ℤ) (m : ℕ) (hm : 1 ≤ m)
      (h : HighModeH1Threshold u n),
      (2 : ℝ) ^ (-(m : ℤ)) * molnarWeight m n ^ 2 *
        action (physicalOfSobolev u) n ≤
          (4 : ℝ) ^ m * higherAction (physicalOfSobolev u) n (2 * m + 1) ∧
      (4 : ℝ) ^ m * higherAction (physicalOfSobolev u) n (2 * m + 1) ≤
        molnarWeight m n ^ 2 * action (physicalOfSobolev u) n)
    (hcast : ∀ (i m : ℕ) (him : i ≤ m) (u : SobolevR m),
      physicalOfSobolev (lowerSobolevCast i m him u) = physicalOfSobolev u)
    (htrace : ∀ (m : ℕ) (hm : 1 ≤ m) (u : SobolevR m),
      HasSum (fun n : ℤ =>
        (4 : ℝ) ^ m * higherAction (physicalOfSobolev u) n (2 * m + 1))
        (signedCharge m u))
    (m : ℕ) (hm : 1 ≤ m) (u : SobolevR m) :
    actionWeightedSumENNReal m (physicalOfSobolev u) ≠ ⊤ ∧
    actionWeightedSum m (physicalOfSobolev u) ≤
      MEstimates.forwardLowConstant m hm u + (2 : ℝ) ^ m * signedCharge m u := by
  set u1 : SobolevR 1 := lowerSobolevCast 1 m hm u with hu1
  set w := physicalOfSobolev u with hw
  have hw1 : physicalOfSobolev u1 = w := hcast 1 m hm u
  set Q := MTwoMode.H1Norm u1 with hQ
  have hQ0 : 0 ≤ Q := H1Norm_nonneg_src u1
  set K := (1 + 16 * Real.pi) ^ (2 * m) * (1 + Q) ^ (4 * m) with hK
  have hK0 : 0 ≤ K := by positivity
  have hH1 : SobolevSquareSummable 1 (physicalFourier w) := by
    rw [← hw1, ← physicalSobolevEmbed_eq_M]
    simpa using (fourierSeq38_mem_iff ((1 : ℕ) : ℝ) _).1
      (NlsGge.GKDefinitionDesign.physicalSobolevEmbed_mem 1 u1)
  have hI : HasSum (fun n : ℤ => action w n) (‖w‖ ^ 2) := actualGapAction_hasSum_E02_38 w hH1
  have hI0 : ∀ n, 0 ≤ action w n := fun n => actualGapAction_nonneg38 w n
  have hJ := htrace m hm u
  have hJ0 : ∀ n, 0 ≤ (4 : ℝ) ^ m * higherAction w n (2 * m + 1) := fun n =>
    mul_nonneg (by positivity) (NlsGge.ThirdConsultation.M018T.odd_action_nonneg w n m)
  have hle : ∀ n : ℤ, molnarWeight m n ^ 2 * action w n ≤
      K * action w n + (2 : ℝ) ^ m * ((4 : ℝ) ^ m * higherAction w n (2 * m + 1)) := by
    intro n
    by_cases hh : HighModeH1Threshold u1 n
    · have h := (hcomp u1 n m hm hh).1
      rw [hw1] at h
      have h2 : (2 : ℝ) ^ m * ((2 : ℝ) ^ (-(m : ℤ)) * molnarWeight m n ^ 2 * action w n) =
          molnarWeight m n ^ 2 * action w n := by
        rw [← mul_assoc, ← mul_assoc, zpow_neg, zpow_natCast, mul_inv_cancel₀ (by positivity), one_mul]
      have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 ^ m)
      rw [h2] at h3
      nlinarith [mul_nonneg hK0 (hI0 n)]
    · have hn : n = 0 ∨ NlsGge.Atomic.M.M054.indexWeight n < 8 * Q ^ 2 := by
        unfold HighModeH1Threshold at hh
        by_cases h0 : n = 0
        · exact Or.inl h0
        · exact Or.inr (lt_of_not_ge (fun h8 => hh ⟨h0, h8⟩))
      have hwK := low_weight_le m Q hQ0 n hn
      have := mul_le_mul_of_nonneg_right hwK (hI0 n)
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ m) (hJ0 n)]
  have hf0 : ∀ n : ℤ, 0 ≤ molnarWeight m n ^ 2 * action w n :=
    fun n => mul_nonneg (sq_nonneg _) (hI0 n)
  have hg : HasSum (fun n : ℤ => K * action w n +
      (2 : ℝ) ^ m * ((4 : ℝ) ^ m * higherAction w n (2 * m + 1)))
      (K * ‖w‖ ^ 2 + (2 : ℝ) ^ m * signedCharge m u) :=
    (hI.mul_left K).add (hJ.mul_left _)
  have hfs : Summable (fun n : ℤ => molnarWeight m n ^ 2 * action w n) :=
    Summable.of_nonneg_of_le hf0 hle hg.summable
  refine ⟨?_, ?_⟩
  · unfold actionWeightedSumENNReal
    rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hfs]
    exact ENNReal.ofReal_ne_top
  · unfold actionWeightedSum
    have h1 := hfs.tsum_le_tsum hle hg.summable
    rw [hg.tsum_eq] at h1
    have h2 : K * ‖w‖ ^ 2 ≤ MEstimates.forwardLowConstant m hm u := by
      unfold MEstimates.forwardLowConstant massCharge
      rw [← hu1, ← hQ, ← hK, ← hw]
      nlinarith [mul_nonneg hK0 (sq_nonneg ‖w‖)]
    linarith

end NlsGge.ThirdConsultation.M035C
