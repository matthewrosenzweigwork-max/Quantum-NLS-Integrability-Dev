import Mathlib
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W05FiniteGap38
import NlsGge.Atomic.R.R102

                                                                                                                       
                                                                                                                        
                                                                                                                        
                                                                                                                     
                                                                                                                         
                                                                                                               
                                                                                                                       
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38

namespace NlsGge.Birkhoff
namespace R103Aux

theorem tail_uniform_of (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (hs : s < 3 / 4)
    (x : ℕ → ECarrier38 c s) (xInf : ECarrier38 c s)
    (hx : Tendsto x atTop (𝓝 xInf)) :
    (∀ j : ℕ, Summable (fun n : ℤ =>
      remainderSummand38 c.val (physOfE38 c s (x j)) n)) ∧
    (∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ j : ℕ,
      (∑' n : ℤ, if N < n.natAbs then
        |remainderSummand38 c.val (physOfE38 c s (x j)) n| else 0) < eps) := by
  obtain ⟨M1, hM1⟩ := (((continuous_iotaE38 c s).tendsto xInf).comp hx).norm.bddAbove_range
  have hM1' : ∀ j : ℕ, ‖iotaE38 c s (x j)‖ ≤ max 1 M1 := fun j =>
    (hM1 ⟨j, rfl⟩).trans (le_max_right _ _)
  obtain ⟨CB, hCB, hdom⟩ := B.remainderSummand_dominated_phys38 c (max 1 M1) (le_max_left _ _)
  obtain ⟨M2, hM2⟩ :=
    ((((B.weightedHomeoE38 O c s).continuous.tendsto xInf).comp hx).norm).bddAbove_range
  have hz : ∀ j : ℕ, ‖B.weightedHomeoE38 O c s (x j)‖ ≤ max 0 M2 := fun j =>
    (hM2 ⟨j, rfl⟩).trans (le_max_right _ _)
  have hf : ∀ (j : ℕ) (n : ℤ), |remainderSummand38 c.val (physOfE38 c s (x j)) n| ≤
      CB * (tailWeight38 c.val n * ‖eCoe38 c s (B.weightedHomeoE38 O c s (x j)) n‖ ^ 2) := by
    intro j n
    have hsob := sobolev_physOfE38 c s 1 (x j)
    have hn : ‖physicalSobolevL2 1 (physOfE38 c s (x j)) hsob‖ ≤ max 1 M1 := by
      rw [norm_physicalSobolevL2_physOfE38]; exact hM1' j
    have := hdom (physOfE38 c s (x j)) hsob hn n
    rwa [B.Φ_physOfE38 c s (x j), ← B.eCoe_weightedHomeoE38 c s O (x j)] at this
  refine ⟨fun j => ?_, fun eps heps => ?_⟩
  · refine Summable.of_norm_bounded
      (((hasSum_norm_sq_eCarrier38 c s (B.weightedHomeoE38 O c s (x j))).summable.mul_left
        (1 ^ (2 * s - 3 / 2))).mul_left CB) (fun n => ?_)
    rw [Real.norm_eq_abs]
    exact (hf j n).trans (mul_le_mul_of_nonneg_left
      (tailWeight_mul_le38 c s hs.le 1 one_pos n (japaneseBracket_one_le n) _) hCB.le)
  · have hjb : Tendsto (fun N : ℕ => japaneseBracket (N : ℤ)) atTop atTop := by
      refine tendsto_atTop_mono (fun N => ?_) tendsto_natCast_atTop_atTop
      unfold japaneseBracket
      refine Real.le_sqrt_of_sq_le ?_
      push_cast
      nlinarith
    have hpow : Tendsto (fun N : ℕ => japaneseBracket (N : ℤ) ^ (2 * s - 3 / 2)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (y := 3 / 2 - 2 * s) (by linarith)).comp hjb
      have e : -(3 / 2 - 2 * s) = 2 * s - 3 / 2 := by ring
      rw [e] at h
      exact h
    have hK := hpow.const_mul (CB * (max 0 M2) ^ 2)
    rw [mul_zero] at hK
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hK.eventually (gt_mem_nhds heps))
    refine ⟨N, fun j => ?_⟩
    set z := B.weightedHomeoE38 O c s (x j) with hzdef
    obtain ⟨hRs, hRle⟩ := NlsGge.ThirdConsultation.R.remainder_majorant_tail c s hs z N
    have hpt : ∀ n : ℤ, (if N < n.natAbs then |remainderSummand38 c.val (physOfE38 c s (x j)) n| else 0) ≤
        CB * (if N < n.natAbs then fullWeightRate c.val n * ‖eCoe38 c s z n‖ ^ 2 *
          Real.rpow (japaneseBracket n) (-(3 / 2 : ℝ)) else 0) := fun n => by
      split_ifs
      · refine (hf j n).trans (le_of_eq ?_)
        unfold tailWeight38
        simp only [Real.rpow_eq_pow]
        ring
      · simp
    have hsumL : Summable (fun n : ℤ => if N < n.natAbs then
        |remainderSummand38 c.val (physOfE38 c s (x j)) n| else 0) :=
      Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp [abs_nonneg]) hpt (hRs.mul_left CB)
    have hz2 : ‖z‖ ^ 2 ≤ (max 0 M2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hz j) 2
    have hr0 : 0 ≤ Real.rpow (japaneseBracket (N : ℤ)) (2 * s - 3 / 2) :=
      Real.rpow_nonneg (japaneseBracket_pos _).le _
    calc (∑' n : ℤ, if N < n.natAbs then |remainderSummand38 c.val (physOfE38 c s (x j)) n| else 0)
        ≤ ∑' n : ℤ, CB * (if N < n.natAbs then fullWeightRate c.val n * ‖eCoe38 c s z n‖ ^ 2 *
            Real.rpow (japaneseBracket n) (-(3 / 2 : ℝ)) else 0) :=
          Summable.tsum_le_tsum hpt hsumL (hRs.mul_left CB)
      _ = CB * ∑' n : ℤ, (if N < n.natAbs then fullWeightRate c.val n * ‖eCoe38 c s z n‖ ^ 2 *
            Real.rpow (japaneseBracket n) (-(3 / 2 : ℝ)) else 0) := tsum_mul_left
      _ ≤ CB * (Real.rpow (japaneseBracket (N : ℤ)) (2 * s - 3 / 2) * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hRle hCB.le
      _ ≤ CB * (Real.rpow (japaneseBracket (N : ℤ)) (2 * s - 3 / 2) * (max 0 M2) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz2 hr0) hCB.le
      _ < eps := by
          have := hN N le_rfl
          simp only [Real.rpow_eq_pow] at this ⊢
          linarith [show CB * (japaneseBracket (N : ℤ) ^ (2 * s - 3 / 2) * max 0 M2 ^ 2) =
            CB * max 0 M2 ^ 2 * japaneseBracket (N : ℤ) ^ (2 * s - 3 / 2) by ring]

end R103Aux
end NlsGge.Birkhoff
