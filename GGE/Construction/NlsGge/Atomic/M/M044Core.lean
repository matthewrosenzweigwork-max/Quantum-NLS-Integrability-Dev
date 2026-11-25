import Mathlib
import NlsGge.ThirdConsultation.M.M044Host
import NlsGge.Atomic.M.M035Core
import NlsGge.Atomic.M.M014
import NlsGge.Atomic.M.M010Host
import NlsGge.ThirdConsultation.M.SpectralRadiusHost

                                                                                                                  
                                                                                  
                                                                                                            
                                                                                                   
                                                                                                                        
                                                                                       
                                                                                                        
                                                                                                                      
                                                                                                            
                                                                           
                                                                                                              
                                             
                                                                                                                     
                                                                                                                    
                                                                                                                
                                                                                                                    
                                                                                                
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.GKDefinitionDesign NlsGge.Birkhoff
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.M044C

open NlsGge.ThirdConsultation.M

theorem summable_of_ennreal (f : ℤ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (h : (∑' n : ℤ, ENNReal.ofReal (f n)) ≠ ⊤) : Summable f := by
  have := ENNReal.summable_toReal h
  convert this using 1
  funext n; rw [ENNReal.toReal_ofReal (hf n)]

/-- Moment comparison on a gap contained in [−R, R]. -/
theorem moment_le_of_radius (w : PhysicalL2) (n : ℤ) (m : ℕ) (hm : 1 ≤ m) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∀ x ∈ Set.Icc (actualGapLowerAllE02_38 w n) (actualGapUpperAllE02_38 w n), |x| ≤ R) :
    higherAction w n (2 * m + 1) ≤ R ^ (2 * m - 2) * higherAction w n 3 := by
  obtain ⟨-, -, hi1, -, he1⟩ := higher_action_gap_integral w n (2 * m + 1) (by omega)
  obtain ⟨-, -, hi3, -, he3⟩ := higher_action_gap_integral w n 3 (by omega)
  rw [show 2 * m + 1 - 1 = 2 * m by omega] at hi1 he1
  rw [he1, he3]
  have hab : periodicMinus w n ≤ periodicPlus w n := (gap_endpoint_levels38 w n).1
  have hmono : (∫ x in periodicMinus w n..periodicPlus w n, x ^ (2 * m) * spectralHeight w n x) ≤
      ∫ x in periodicMinus w n..periodicPlus w n, R ^ (2 * m - 2) * (x ^ (3 - 1) * spectralHeight w n x) := by
    refine intervalIntegral.integral_mono_on hab hi1 (hi3.const_mul _) ?_
    intro x hx
    have hxR : |x| ≤ R := hR x hx
    have hh : 0 ≤ spectralHeight w n x := actualGapHeightE02_38_nonneg w x
    have hx2 : x ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) hxR 2
    have hpow : x ^ (2 * m) ≤ R ^ (2 * m - 2) * x ^ 2 := by
      have e1 : x ^ (2 * m) = (x ^ 2) ^ (m - 1) * x ^ 2 := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      have e2 : R ^ (2 * m - 2) = (R ^ 2) ^ (m - 1) := by
        rw [← pow_mul]; congr 1; omega
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg x) hx2 _) (sq_nonneg x)
    rw [show 3 - 1 = 2 by norm_num]
    nlinarith [mul_le_mul_of_nonneg_right hpow hh]
  rw [intervalIntegral.integral_const_mul] at hmono
  have hpi : 0 ≤ 2 / Real.pi := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmono hpi]

/-- On a gap inside [−1/2, 1/2]: 4^m J_(2m+1) ≤ I. -/
theorem zero_moment_le (w : PhysicalL2) (n : ℤ) (m : ℕ)
    (hR : ∀ x ∈ Set.Icc (actualGapLowerAllE02_38 w n) (actualGapUpperAllE02_38 w n), |x| ≤ (1 / 2 : ℝ)) :
    (4 : ℝ) ^ m * higherAction w n (2 * m + 1) ≤ action w n := by
  obtain ⟨-, -, hi1, -, he1⟩ := higher_action_gap_integral w n (2 * m + 1) (by omega)
  rw [show 2 * m + 1 - 1 = 2 * m by omega] at hi1 he1
  rw [he1]
  have hab : periodicMinus w n ≤ periodicPlus w n := (gap_endpoint_levels38 w n).1
  have hint : IntervalIntegrable (fun x => spectralHeight w n x) volume (periodicMinus w n) (periodicPlus w n) :=
    intervalIntegrable_actualGapHeightE02_38 w _ _
  have hmono : (∫ x in periodicMinus w n..periodicPlus w n, x ^ (2 * m) * spectralHeight w n x) ≤
      ∫ x in periodicMinus w n..periodicPlus w n, ((1 : ℝ) / 4) ^ m * spectralHeight w n x := by
    refine intervalIntegral.integral_mono_on hab hi1 (hint.const_mul _) ?_
    intro x hx
    have hh : 0 ≤ spectralHeight w n x := actualGapHeightE02_38_nonneg w x
    have hx2 : x ^ 2 ≤ 1 / 4 := by
      have := hR x hx
      nlinarith [abs_nonneg x, sq_abs x]
    have : x ^ (2 * m) ≤ ((1 : ℝ) / 4) ^ m := by
      rw [pow_mul]; exact pow_le_pow_left₀ (sq_nonneg x) hx2 m
    exact mul_le_mul_of_nonneg_right this hh
  rw [intervalIntegral.integral_const_mul] at hmono
  have e : action w n = (2 / Real.pi) * ∫ x in periodicMinus w n..periodicPlus w n, spectralHeight w n x := rfl
  rw [e]
  have h4 : (4 : ℝ) ^ m * ((1 : ℝ) / 4) ^ m = 1 := by rw [← mul_pow]; norm_num
  have hpi : 0 ≤ 2 / Real.pi := by positivity
  have := mul_le_mul_of_nonneg_left hmono (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 ^ m) hpi)
  calc (4 : ℝ) ^ m * (2 / Real.pi * ∫ x in periodicMinus w n..periodicPlus w n, x ^ (2 * m) * spectralHeight w n x)
      = (4 ^ m * (2 / Real.pi)) * ∫ x in periodicMinus w n..periodicPlus w n, x ^ (2 * m) * spectralHeight w n x := by ring
    _ ≤ (4 ^ m * (2 / Real.pi)) * (((1 : ℝ) / 4) ^ m * ∫ x in periodicMinus w n..periodicPlus w n, spectralHeight w n x) := this
    _ = 2 / Real.pi * ∫ x in periodicMinus w n..periodicPlus w n, spectralHeight w n x := by
        rw [show (4 : ℝ) ^ m * (2 / Real.pi) * (((1 : ℝ) / 4) ^ m * ∫ x in periodicMinus w n..periodicPlus w n, spectralHeight w n x)
          = ((4 : ℝ) ^ m * ((1 : ℝ) / 4) ^ m) * (2 / Real.pi * ∫ x in periodicMinus w n..periodicPlus w n, spectralHeight w n x) by ring, h4, one_mul]

/-- The final scalar inequality of the r16 route (m = j + 1). -/
theorem remainder_le (j : ℕ) (A0 A1 Q S : ℝ) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hS0 : 0 ≤ S) (hQ : 0 ≤ Q)
    (hQ2 : Q ^ 2 ≤ 3 * ((1 + A0) * A1)) (hS : S ≤ 2 * ((1 + A0) * A1)) :
    (4 : ℝ) ^ j * (8 * Real.pi * Q ^ 2) ^ (2 * j) * S ≤
      (64 * Real.pi) ^ (2 * (j + 1)) * (1 + A0) ^ (2 * (j + 1) - 1) * A1 ^ (2 * (j + 1) - 1) := by
  set X := (1 + A0) * A1 with hX
  have hX0 : 0 ≤ X := by positivity
  have hpi := Real.pi_pos
  have e1 : (2 * (j + 1) - 1) = 2 * j + 1 := by omega
  have hXp : (1 + A0) ^ (2 * j + 1) * A1 ^ (2 * j + 1) = X ^ (2 * j + 1) := by rw [hX, mul_pow]
  rw [e1, show (64 * Real.pi) ^ (2 * (j + 1)) * (1 + A0) ^ (2 * j + 1) * A1 ^ (2 * j + 1) =
      (64 * Real.pi) ^ (2 * (j + 1)) * X ^ (2 * j + 1) by rw [← hXp]; ring]
  have hq : (8 * Real.pi * Q ^ 2) ^ (2 * j) ≤ (8 * Real.pi * (3 * X)) ^ (2 * j) :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hQ2 (by positivity)) _
  have step1 : (4 : ℝ) ^ j * (8 * Real.pi * Q ^ 2) ^ (2 * j) * S ≤
      (4 : ℝ) ^ j * (8 * Real.pi * (3 * X)) ^ (2 * j) * (2 * X) := by
    have := mul_le_mul hq hS hS0 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 4 ^ j)]
  have e2 : (4 : ℝ) ^ j * (8 * Real.pi * (3 * X)) ^ (2 * j) * (2 * X) =
      2 * (48 * Real.pi) ^ (2 * j) * X ^ (2 * j + 1) := by
    have a1 : (4 : ℝ) ^ j = 2 ^ (2 * j) := by rw [pow_mul]; norm_num
    have a2 : (8 * Real.pi * (3 * X)) ^ (2 * j) = (8 * Real.pi) ^ (2 * j) * 3 ^ (2 * j) * X ^ (2 * j) := by
      rw [mul_pow, mul_pow]; ring
    have a3 : (48 * Real.pi) ^ (2 * j) = 2 ^ (2 * j) * (8 * Real.pi) ^ (2 * j) * 3 ^ (2 * j) := by
      rw [show (48 : ℝ) * Real.pi = 2 * (8 * Real.pi) * 3 by ring, mul_pow, mul_pow]
    rw [a1, a2, a3, pow_succ]; ring
  have hc : 2 * (48 * Real.pi) ^ (2 * j) ≤ (64 * Real.pi) ^ (2 * (j + 1)) := by
    have h1 : (48 * Real.pi) ^ (2 * j) ≤ (64 * Real.pi) ^ (2 * j) :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    have h2 : (2 : ℝ) ≤ (64 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
    nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 64 * Real.pi) (2 * j)]
  rw [e2] at step1
  have := mul_le_mul_of_nonneg_right hc (pow_nonneg hX0 (2 * j + 1))
  linarith

theorem odd_trace_core
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
    (hzero : ∀ (u : SobolevR 1) (hsmall : MTwoMode.H1Norm u ≤ (1 / 4 : ℝ)),
      ∀ x : ℝ, x ∈ closedGap (physicalOfSobolev u) 0 → |x| ≤ (1 / 2 : ℝ))
    (hcentral : ∀ (u : SobolevR 1) (hlarge : (1 / 4 : ℝ) ≤ MTwoMode.H1Norm u)
      (n : ℤ) (hn : n = 0 ∨ LowModeH1Threshold u n),
      ∀ x : ℝ, x ∈ closedGap (physicalOfSobolev u) n →
        |x| ≤ MEstimates.spectralRadius u)
    (hseed : ∀ (u : SobolevR 1),
      (1 / 3 : ℝ) * MTwoMode.H1Norm u ^ 2 ≤
        actionWeightedSum 1 (physicalOfSobolev u) +
          actionWeightedSum 0 (physicalOfSobolev u) ^ 2)
    (h041 : ∀ (u : SobolevR 1),
      actionWeightedSumENNReal 1 (physicalOfSobolev u) ≠ ⊤ ∧
      Summable (fun n : ℤ => (2 * (n : ℝ) * Real.pi) ^ 2 *
        action (physicalOfSobolev u) n) ∧
      signedCharge 1 u - 2 * massCharge (physicalOfSobolev u) ^ 2 ≤
        ∑' n : ℤ, (2 * (n : ℝ) * Real.pi) ^ 2 *
          action (physicalOfSobolev u) n)
    (m : ℕ) (hm : 1 ≤ m) (u : SobolevR m) :
    actionWeightedSumENNReal m (physicalOfSobolev u) ≠ ⊤ ∧
    oddTraceEnergy m (physicalOfSobolev u) ≠ ⊤ ∧
    oddTraceSum m (physicalOfSobolev u) ≤
      actionWeightedSum m (physicalOfSobolev u) +
        (64 * Real.pi) ^ (2 * m) *
          (1 + actionWeightedSum 0 (physicalOfSobolev u)) ^ (2 * m - 1) *
          actionWeightedSum 1 (physicalOfSobolev u) ^ (2 * m - 1) := by
  set u1 : SobolevR 1 := lowerSobolevCast 1 m hm u with hu1
  set w := physicalOfSobolev u with hw
  have hw1 : physicalOfSobolev u1 = w := hcast 1 m hm u
  set Q := MTwoMode.H1Norm u1 with hQ
  have hQ0 : 0 ≤ Q := NlsGge.ThirdConsultation.M035C.H1Norm_nonneg_src u1
  have hH1 : SobolevSquareSummable 1 (physicalFourier w) := by
    rw [← hw1, ← physicalSobolevEmbed_eq_M]
    simpa using (fourierSeq38_mem_iff ((1 : ℕ) : ℝ) _).1
      (NlsGge.GKDefinitionDesign.physicalSobolevEmbed_mem 1 u1)
  have hI : HasSum (fun n : ℤ => action w n) (‖w‖ ^ 2) := actualGapAction_hasSum_E02_38 w hH1
  have hI0 : ∀ n, 0 ≤ action w n := fun n => actualGapAction_nonneg38 w n
  have hcore := NlsGge.ThirdConsultation.M035C.forward_core hcomp hcast htrace m hm u
  have hcore1 := NlsGge.ThirdConsultation.M035C.forward_core hcomp hcast htrace 1 le_rfl u1
  rw [hw1] at hcore1
  have hwm0 : ∀ (r : ℕ) (n : ℤ), 0 ≤ molnarWeight r n ^ 2 * action w n :=
    fun r n => mul_nonneg (sq_nonneg _) (hI0 n)
  have hAms : Summable (fun n : ℤ => molnarWeight m n ^ 2 * action w n) := by
    have h := hcore.1; unfold actionWeightedSumENNReal at h
    exact summable_of_ennreal _ (hwm0 m) h
  have hA1s : Summable (fun n : ℤ => molnarWeight 1 n ^ 2 * action w n) := by
    have h := hcore1.1; unfold actionWeightedSumENNReal at h
    exact summable_of_ennreal _ (hwm0 1) h
  have hJ := htrace m hm u
  have hJ0 : ∀ n, 0 ≤ (4 : ℝ) ^ m * higherAction w n (2 * m + 1) := fun n =>
    mul_nonneg (by positivity) (NlsGge.ThirdConsultation.M018T.odd_action_nonneg w n m)
  refine ⟨hcore.1, ?_, ?_⟩
  · unfold oddTraceEnergy
    rw [← ENNReal.ofReal_tsum_of_nonneg hJ0 hJ.summable]
    exact ENNReal.ofReal_ne_top
  -- the action sums
  set Am := actionWeightedSum m w with hAm
  set A0 := actionWeightedSum 0 w with hA0
  set A1 := actionWeightedSum 1 w with hA1
  have hA0e : A0 = ‖w‖ ^ 2 := by
    rw [hA0]; unfold actionWeightedSum
    rw [← hI.tsum_eq]; congr 1; funext n; simp [molnarWeight]
  have hA0n : 0 ≤ A0 := by rw [hA0e]; positivity
  have hA1n : 0 ≤ A1 := tsum_nonneg (hwm0 1)
  have hw1ge : ∀ n : ℤ, (1 : ℝ) ≤ molnarWeight 1 n ^ 2 := by
    intro n; unfold molnarWeight
    have : (1 : ℝ) ≤ 1 + |2 * Real.pi * (n : ℝ)| := by linarith [abs_nonneg (2 * Real.pi * (n : ℝ))]
    nlinarith
  have hA01 : A0 ≤ A1 := by
    rw [hA0e, ← hI.tsum_eq]
    exact hI.summable.tsum_le_tsum (fun n => by nlinarith [hw1ge n, hI0 n]) hA1s
  have hrem0 : 0 ≤ (64 * Real.pi) ^ (2 * m) * (1 + A0) ^ (2 * m - 1) * A1 ^ (2 * m - 1) := by positivity
  unfold oddTraceSum
  by_cases hsmall : Q ≤ (1 / 4 : ℝ)
  · have hle : ∀ n : ℤ, (4 : ℝ) ^ m * higherAction w n (2 * m + 1) ≤ molnarWeight m n ^ 2 * action w n := by
      intro n
      by_cases h0 : n = 0
      · subst h0
        have hz := hzero u1 hsmall
        rw [hw1] at hz
        have := zero_moment_le w 0 m (fun x hx => hz x hx)
        simpa [molnarWeight] using this
      · have hH : HighModeH1Threshold u1 n := by
          refine ⟨h0, ?_⟩
          unfold NlsGge.Atomic.M.M054.indexWeight
          nlinarith [abs_nonneg (n : ℝ)]
        have := (hcomp u1 n m hm hH).2
        rw [hw1] at this
        exact this
    have h := hJ.summable.tsum_le_tsum hle hAms
    have hAmdef : Am = ∑' n : ℤ, molnarWeight m n ^ 2 * action w n := rfl
    rw [← hAmdef] at h
    linarith
  · have hlarge : (1 / 4 : ℝ) ≤ Q := le_of_lt (not_le.1 hsmall)
    set R := MEstimates.spectralRadius u1 with hR
    have hR0 : 0 ≤ R := by rw [hR]; unfold MEstimates.spectralRadius; positivity
    have h3 := htrace 1 le_rfl u1
    rw [hw1] at h3
    set S1 := signedCharge 1 u1 with hS1
    have h3' : HasSum (fun n : ℤ => (4 : ℝ) * higherAction w n 3) S1 := by simpa using h3
    have hJ3 : HasSum (fun n : ℤ => higherAction w n 3) (S1 / 4) := by
      have := h3'.div_const 4
      convert this using 1; funext n; ring
    have hJ30 : ∀ n, 0 ≤ higherAction w n 3 := fun n => by
      simpa using NlsGge.ThirdConsultation.M018T.odd_action_nonneg w n 1
    have hS10 : 0 ≤ S1 := h3'.nonneg (fun n => mul_nonneg (by norm_num) (hJ30 n))
    set c := (4 : ℝ) ^ m * R ^ (2 * m - 2) with hc
    have hc0 : 0 ≤ c := by positivity
    have hle : ∀ n : ℤ, (4 : ℝ) ^ m * higherAction w n (2 * m + 1) ≤
        molnarWeight m n ^ 2 * action w n + c * higherAction w n 3 := by
      intro n
      by_cases hcen : n = 0 ∨ LowModeH1Threshold u1 n
      · have hz := hcentral u1 hlarge n hcen
        rw [hw1] at hz
        have h1 := moment_le_of_radius w n m hm R hR0 (fun x hx => hz x hx)
        have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 ^ m)
        nlinarith [hwm0 m n]
      · push Not at hcen
        have hH : HighModeH1Threshold u1 n := ⟨hcen.1, not_lt.1 hcen.2⟩
        have := (hcomp u1 n m hm hH).2
        rw [hw1] at this
        nlinarith [mul_nonneg hc0 (hJ30 n)]
    have hsum : HasSum (fun n : ℤ => molnarWeight m n ^ 2 * action w n + c * higherAction w n 3)
        (Am + c * (S1 / 4)) := hAms.hasSum.add (hJ3.mul_left c)
    have hmain := hJ.summable.tsum_le_tsum hle hsum.summable
    rw [hsum.tsum_eq] at hmain
    -- seed and M-041
    have hseed1 := hseed u1
    rw [hw1] at hseed1
    have hQ2 : Q ^ 2 ≤ 3 * ((1 + A0) * A1) := by
      have : A0 ^ 2 ≤ A0 * A1 := by nlinarith
      nlinarith
    obtain ⟨-, h41s, h41⟩ := h041 u1
    rw [hw1] at h41s h41
    have hM : massCharge w = A0 := by rw [hA0e]; rfl
    rw [hM] at h41
    have hpt : ∀ n : ℤ, (2 * (n : ℝ) * Real.pi) ^ 2 * action w n + action w n ≤
        molnarWeight 1 n ^ 2 * action w n := by
      intro n
      have hsq : (2 * (n : ℝ) * Real.pi) ^ 2 = |2 * Real.pi * (n : ℝ)| ^ 2 := by
        rw [sq_abs]; ring
      have hw : (2 * (n : ℝ) * Real.pi) ^ 2 + 1 ≤ molnarWeight 1 n ^ 2 := by
        unfold molnarWeight; rw [hsq]; nlinarith [abs_nonneg (2 * Real.pi * (n : ℝ))]
      calc (2 * (n : ℝ) * Real.pi) ^ 2 * action w n + action w n
          = ((2 * (n : ℝ) * Real.pi) ^ 2 + 1) * action w n := by ring
        _ ≤ molnarWeight 1 n ^ 2 * action w n := mul_le_mul_of_nonneg_right hw (hI0 n)
    have hsub : (∑' n : ℤ, (2 * (n : ℝ) * Real.pi) ^ 2 * action w n) + A0 ≤ A1 := by
      have h := (h41s.add hI.summable).tsum_le_tsum hpt hA1s
      rw [h41s.tsum_add hI.summable] at h
      rw [hA0e, ← hI.tsum_eq]
      exact h
    have hsq : A0 ^ 2 ≤ A0 * A1 := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hA01 hA0n
    have hS : S1 ≤ 2 * ((1 + A0) * A1) := by
      have e : 2 * ((1 + A0) * A1) = 2 * A1 + 2 * (A0 * A1) := by ring
      rw [e]; linarith
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hrem := remainder_le j A0 A1 Q S1 hA0n hA1n hS10 hQ0 hQ2 hS
    have hcS : c * (S1 / 4) = (4 : ℝ) ^ j * (8 * Real.pi * Q ^ 2) ^ (2 * j) * S1 := by
      rw [hc, hR]; unfold MEstimates.spectralRadius
      rw [show 2 * (j + 1) - 2 = 2 * j by omega, pow_succ]; ring
    linarith

end NlsGge.ThirdConsultation.M044C
