import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W05FiniteGap38
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

                                                                                                                      
                                                                                                                          
                                                                                             
                                                                                                                          
                                                                                                                           
                                                                                                                                                                              
                                                                                                                                  
                                                                                   
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem remainder_majorant_tail {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (hs : s < 3 / 4)
    (x : ECarrier38 c s) (N : ℕ) :
    Summable (fun n : ℤ => if N < n.natAbs then
      fullWeightRate c.val n * ‖eCoe38 c s x n‖ ^ 2 *
        Real.rpow (japaneseBracket n) (-(3 / 2 : ℝ)) else 0) ∧
    (∑' n : ℤ, if N < n.natAbs then
      fullWeightRate c.val n * ‖eCoe38 c s x n‖ ^ 2 *
        Real.rpow (japaneseBracket n) (-(3 / 2 : ℝ)) else 0) ≤
      Real.rpow (japaneseBracket (N : ℤ)) (2 * s - 3 / 2) * ‖x‖ ^ 2 := by
  obtain ⟨hlo, -, hc⟩ := c.property
  have hrate : ∀ n : ℤ, 0 < fullWeightRate c.val n :=
    fullWeightRate_pos lo up c.val hlo (fun j => (hc j).1) (fun j => (hc j).2)
  have hg := (hasSum_norm_sq_eCarrier38 c s x).mul_left
    (Real.rpow (japaneseBracket (N : ℤ)) (2 * s - 3 / 2))
  have hf0 : ∀ n : ℤ, 0 ≤ (if N < n.natAbs then
      fullWeightRate c.val n * ‖eCoe38 c s x n‖ ^ 2 *
        Real.rpow (japaneseBracket n) (-(3 / 2 : ℝ)) else 0) := fun n => by
    split_ifs
    · exact mul_nonneg (mul_nonneg (hrate n).le (sq_nonneg _)) (Real.rpow_nonneg (japaneseBracket_pos n).le _)
    · exact le_rfl
  have hle : ∀ n : ℤ, (if N < n.natAbs then
      fullWeightRate c.val n * ‖eCoe38 c s x n‖ ^ 2 *
        Real.rpow (japaneseBracket n) (-(3 / 2 : ℝ)) else 0) ≤
      Real.rpow (japaneseBracket (N : ℤ)) (2 * s - 3 / 2) *
        (fullModeWeight c s n * ‖eCoe38 c s x n‖ ^ 2) := fun n => by
    have hr0 : 0 ≤ Real.rpow (japaneseBracket (N : ℤ)) (2 * s - 3 / 2) :=
      Real.rpow_nonneg (japaneseBracket_pos _).le _
    have hm0 : 0 ≤ fullModeWeight c s n * ‖eCoe38 c s x n‖ ^ 2 :=
      mul_nonneg (fullModeWeight_pos c s n).le (sq_nonneg _)
    split_ifs with h
    · have hjb : japaneseBracket (N : ℤ) ≤ japaneseBracket n := by
        unfold japaneseBracket
        refine Real.sqrt_le_sqrt ?_
        have h1 : ((N : ℤ) : ℝ) ≤ |(n : ℝ)| := by
          have : (N : ℤ) ≤ |n| := by
            rw [Int.abs_eq_natAbs]; exact_mod_cast h.le
          exact_mod_cast this
        have h2 : (0 : ℝ) ≤ ((N : ℤ) : ℝ) := by positivity
        nlinarith [sq_abs (n : ℝ)]
      have key := tailWeight_mul_le38 c s hs.le (japaneseBracket (N : ℤ)) (japaneseBracket_pos _) n hjb
        (eCoe38 c s x n)
      unfold tailWeight38 at key
      simp only [Real.rpow_eq_pow] at key ⊢
      calc fullWeightRate c.val n * ‖eCoe38 c s x n‖ ^ 2 * japaneseBracket n ^ (-(3 / 2 : ℝ))
          = fullWeightRate c.val n * japaneseBracket n ^ (-(3 / 2) : ℝ) * ‖eCoe38 c s x n‖ ^ 2 := by
            norm_num; ring
        _ ≤ _ := key
    · exact mul_nonneg hr0 hm0
  have hs1 := Summable.of_nonneg_of_le hf0 hle hg.summable
  refine ⟨hs1, ?_⟩
  calc (∑' n : ℤ, if N < n.natAbs then
        fullWeightRate c.val n * ‖eCoe38 c s x n‖ ^ 2 *
          Real.rpow (japaneseBracket n) (-(3 / 2 : ℝ)) else 0)
      ≤ ∑' n : ℤ, Real.rpow (japaneseBracket (N : ℤ)) (2 * s - 3 / 2) *
          (fullModeWeight c s n * ‖eCoe38 c s x n‖ ^ 2) := Summable.tsum_le_tsum hle hs1 hg.summable
    _ = Real.rpow (japaneseBracket (N : ℤ)) (2 * s - 3 / 2) * ‖x‖ ^ 2 := hg.tsum_eq

end NlsGge.ThirdConsultation.R
