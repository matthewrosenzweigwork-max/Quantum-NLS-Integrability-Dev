import Mathlib
import NlsGge.Atomic.M.M033
import NlsGge.Atomic.G6.G6028
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompat
import NlsGge.ThirdConsultation.M.Round5b

                                                                            
                                                                                                           
                                                                                                
                                                                                                                          
                                                                                                       
                                                                                                                          
                                                                                                                 
                                                                                                                      
                                                                                       
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.MOddSum

open NlsGge.ThirdConsultation.M

/-- Lowering the Sobolev index does not change the physical field. -/
theorem physicalOfSobolev_lowerSobolevCast (i m : ℕ) (him : i ≤ m) (u : SobolevR m) :
    physicalOfSobolev (lowerSobolevCast i m him u) = physicalOfSobolev u := by
  rw [← NlsGge.GKDefinitionDesign.physicalSobolevEmbed_eq_M,
    ← NlsGge.GKDefinitionDesign.physicalSobolevEmbed_eq_M]
  apply fourierSeq38_injective
  funext n
  rw [NlsGge.GKDefinitionDesign.physicalSobolevEmbed_fourier,
    NlsGge.GKDefinitionDesign.physicalSobolevEmbed_fourier]
  unfold lowerSobolevCast
  rw [LinearIsometryEquiv.apply_symm_apply, carrierCoe38_incl38]

/-- Molnar weight versus the house Sobolev weight. -/
theorem molnar_sq_le (m : ℕ) (n : ℤ) :
    molnarWeight m n ^ 2 ≤
      (2 * (1 + 2 * Real.pi) ^ 2) ^ m * Real.rpow (japaneseBracket n) (2 * (m : ℝ)) := by
  have hj : Real.rpow (japaneseBracket n) (2 * (m : ℝ)) = (1 + (n : ℝ) ^ 2) ^ m := by
    show japaneseBracket n ^ (2 * (m : ℝ)) = _
    rw [show (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul]
    unfold japaneseBracket
    rw [Real.sq_sqrt (by positivity)]
  rw [hj]
  unfold molnarWeight
  rw [← pow_mul, mul_comm m 2, pow_mul, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have ha : |2 * Real.pi * (n : ℝ)| = 2 * Real.pi * |(n : ℝ)| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [ha]
  have hn0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : 1 + 2 * Real.pi * |(n : ℝ)| ≤ (1 + 2 * Real.pi) * (1 + |(n : ℝ)|) := by nlinarith
  have h2 : (1 + |(n : ℝ)|) ^ 2 ≤ 2 * (1 + (n : ℝ) ^ 2) := by
    nlinarith [sq_abs (n : ℝ), sq_nonneg (1 - |(n : ℝ)|)]
  calc (1 + 2 * Real.pi * |(n : ℝ)|) ^ 2 ≤ ((1 + 2 * Real.pi) * (1 + |(n : ℝ)|)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
    _ = (1 + 2 * Real.pi) ^ 2 * (1 + |(n : ℝ)|) ^ 2 := by ring
    _ ≤ (1 + 2 * Real.pi) ^ 2 * (2 * (1 + (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * (1 + 2 * Real.pi) ^ 2 * (1 + (n : ℝ) ^ 2) := by ring

/-- Finite weighted action energy of an H^m field (G6-023 + action identity). -/
theorem weighted_action_summable (m : ℕ) (u : SobolevR m) :
    Summable (fun n : ℤ => molnarWeight m n ^ 2 * action (physicalOfSobolev u) n) := by
  have hmem := NlsGge.GKDefinitionDesign.birkhoffSobolev_mem m u
  rw [NlsGge.GKDefinitionDesign.physicalSobolevEmbed_eq_M, mem_seqSobolev38_iff] at hmem
  unfold SobolevSquareSummable at hmem
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (sq_nonneg _) (NlsGge.GKDefinitionDesign.realActionNonneg38 _ n))
    (fun n => ?_) (hmem.mul_left ((2 * (1 + 2 * Real.pi) ^ 2) ^ m))
  have hI : action (physicalOfSobolev u) n =
      ‖(NlsGge.GKDefinitionDesign.physicalBirkhoff (physicalOfSobolev u) : ℤ → ℂ) n‖ ^ 2 :=
    (NlsGge.GKDefinitionDesign.G6028.1 (physicalOfSobolev u) n).2.2
  rw [hI, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (molnar_sq_le m n) (sq_nonneg _)

/-- Only finitely many labels fail the high H1 threshold. -/
theorem nonHigh_finite (u : SobolevR 1) :
    {n : ℤ | ¬ HighModeH1Threshold u n}.Finite := by
  set K : ℕ := ⌈8 * MTwoMode.H1Norm u ^ 2⌉₊
  refine (Finset.Icc (-(K : ℤ)) K).finite_toSet.subset (fun n hn => ?_)
  simp only [Set.mem_setOf_eq, HighModeH1Threshold, not_and_or, not_not, not_le] at hn
  simp only [Finset.coe_Icc, Set.mem_Icc]
  rcases hn with h0 | hlt
  · subst h0; constructor <;> simp
  · unfold NlsGge.Atomic.M.M054.indexWeight at hlt
    have hK : 8 * MTwoMode.H1Norm u ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
    have habs : |(n : ℝ)| < K := by linarith [abs_nonneg (n : ℝ)]
    have h2 : |n| < (K : ℤ) := by exact_mod_cast habs
    constructor <;> linarith [abs_lt.mp h2]

end NlsGge.ThirdConsultation.MOddSum

namespace NlsGge.ThirdConsultation.M

theorem odd_higher_action_summable
    (m : ℕ) (hm : 1 ≤ m) (u : SobolevR m) :
    Summable (fun n : ℤ =>
      (4 : ℝ) ^ m * higherAction (physicalOfSobolev u) n (2 * m + 1)) := by
  set u1 : SobolevR 1 := lowerSobolevCast 1 m hm u with hu1
  have hP : physicalOfSobolev u1 = physicalOfSobolev u :=
    NlsGge.ThirdConsultation.MOddSum.physicalOfSobolev_lowerSobolevCast 1 m hm u
  have hsum := NlsGge.ThirdConsultation.MOddSum.weighted_action_summable m u
  refine Summable.of_norm_bounded_eventually hsum ?_
  rw [Filter.eventually_cofinite]
  refine (NlsGge.ThirdConsultation.MOddSum.nonHigh_finite u1).subset (fun n hn => ?_)
  simp only [Set.mem_setOf_eq] at hn ⊢
  intro hhigh
  apply hn
  obtain ⟨hlo, hhi⟩ := high_odd_action_comparison u1 n m hm hhigh
  rw [hP] at hlo hhi
  have h0 : 0 ≤ (2 : ℝ) ^ (-(m : ℤ)) * molnarWeight m n ^ 2 * action (physicalOfSobolev u) n :=
    mul_nonneg (mul_nonneg (zpow_nonneg (by norm_num) _) (sq_nonneg _))
      (NlsGge.GKDefinitionDesign.realActionNonneg38 _ n)
  rw [Real.norm_eq_abs, abs_of_nonneg (h0.trans hlo)]
  exact hhi

end NlsGge.ThirdConsultation.M
