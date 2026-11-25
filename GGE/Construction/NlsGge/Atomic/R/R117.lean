import Mathlib
import NlsGge.Birkhoff.W08Compact38

                                                                                                          
                                                                                                    
                                                                                                                      
                                                                                                                        
                                                   

set_option autoImplicit false
namespace NlsGge.ClaudeH1.R117
open NlsGge.Birkhoff NlsGge.Pilot NlsGge.Sobolev38 NlsGge.SpectralFoundations
open Filter Topology Metric

theorem tailN1 (N : ℕ) (y : H2_38) :
    ‖compl38 ((1 : ℕ) : ℝ) N (i21_38 y)‖ ≤ (japaneseBracket ((N : ℤ) + 1))⁻¹ * ‖y‖ := by
  have hB : (japaneseBracket ((N : ℤ) + 1)) ^ 2 = 1 + ((N : ℝ) + 1) ^ 2 := by
    unfold japaneseBracket
    rw [Real.sq_sqrt (by positivity)]
    push_cast; ring
  have hpos : 0 < japaneseBracket ((N : ℤ) + 1) := japaneseBracket_pos _
  set a := compl38 ((1 : ℕ) : ℝ) N (i21_38 y) with ha
  have h1 := carrier_hasSum_norm_sq38 ((1 : ℕ) : ℝ) a
  have h2 := (carrier_hasSum_norm_sq38 (((1 + 1 : ℕ)) : ℝ) y).mul_left
    ((japaneseBracket ((N : ℤ) + 1))⁻¹ ^ 2)
  have hle : ‖a‖ ^ 2 ≤ (japaneseBracket ((N : ℤ) + 1))⁻¹ ^ 2 * ‖y‖ ^ 2 := by
    refine hasSum_le (fun n => ?_) h1 h2
    have han : carrierCoe38 ((1 : ℕ) : ℝ) a n =
        carrierCoe38 ((1 : ℕ) : ℝ) (i21_38 y) n -
          (if n ∈ symmetricModes N then carrierCoe38 ((1 : ℕ) : ℝ) (i21_38 y) n else 0) := rfl
    have hw1 : sobolevModeWeight ((1 : ℕ) : ℝ) n = 1 + (n : ℝ) ^ 2 := by
      rw [sobolevModeWeight_natCast_F01_38]; ring
    have hw2 : sobolevModeWeight (((1 + 1 : ℕ)) : ℝ) n = (1 + (n : ℝ) ^ 2) ^ 2 := by
      rw [sobolevModeWeight_natCast_F01_38]
    rw [hw1, hw2, han]
    by_cases hn : n ∈ symmetricModes N
    · rw [ite_eq_left_iff.2 (fun h => absurd hn h), sub_self]; simp only [norm_zero]
      rw [zero_pow two_ne_zero, mul_zero]; positivity
    · rw [ite_eq_right_iff.2 (fun h => absurd h hn), sub_zero, carrierCoe38_i21]
      have hn' : (N : ℝ) + 1 ≤ |(n : ℝ)| := by
        have : (N : ℤ) + 1 ≤ |n| := by
          unfold symmetricModes at hn
          rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
          rcases hn with h | h
          · rw [abs_of_neg (by omega)]; omega
          · rw [abs_of_pos (by omega)]; omega
        exact_mod_cast this
      have hsq : 1 + ((N : ℝ) + 1) ^ 2 ≤ 1 + (n : ℝ) ^ 2 := by
        have : ((N : ℝ) + 1) ^ 2 ≤ |(n : ℝ)| ^ 2 := by
          nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
        rw [sq_abs] at this
        linarith
      rw [inv_pow, hB]
      have ht : 0 ≤ ‖carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y n‖ ^ 2 := sq_nonneg _
      generalize ‖carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y n‖ ^ 2 = t at ht ⊢
      have hp : 0 < 1 + ((N : ℝ) + 1) ^ 2 := by positivity
      have hq : 0 < 1 + (n : ℝ) ^ 2 := by positivity
      rw [← sub_nonneg]
      have e : (1 + ((N : ℝ) + 1) ^ 2)⁻¹ * ((1 + (n : ℝ) ^ 2) ^ 2 * t) - (1 + (n : ℝ) ^ 2) * t =
          (1 + (n : ℝ) ^ 2) * t * ((1 + (n : ℝ) ^ 2) - (1 + ((N : ℝ) + 1) ^ 2)) /
            (1 + ((N : ℝ) + 1) ^ 2) := by
        field_simp
      rw [e]
      apply div_nonneg _ hp.le
      exact mul_nonneg (mul_nonneg hq.le ht) (by linarith)
  have hle' : ‖a‖ ^ 2 ≤ ((japaneseBracket ((N : ℤ) + 1))⁻¹ * ‖y‖) ^ 2 := by
    rw [mul_pow]; exact hle
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.2 hpos.le) (norm_nonneg _))).1 hle'

theorem R117_main : ((
  ∀ R : ℝ,
    IsCompact (closure (ballH1 R)) ∧
    TotallyBounded (ballH1 R) ∧
    (∀ N : ℕ, FiniteDimensional ℝ (LinearMap.range (projLin38 ((1 : ℕ) : ℝ) N))) ∧
    (∀ (N : ℕ) (x : H2_38), ‖x‖ ≤ R →
      ‖i21_38 x - projC38 ((1 : ℕ) : ℝ) N (i21_38 x)‖ ≤ (japaneseBracket ((N : ℤ) + 1))⁻¹ * R)
  : Prop)) := by
  intro R
  refine ⟨isCompact_closure_ballH1 R,
    (isCompact_closure_ballH1 R).totallyBounded.subset subset_closure,
    fun N => finiteDimensional_range_projC38_W08 ((1 : ℕ) : ℝ) N, ?_⟩
  intro N x hx
  have hc : i21_38 x - projC38 ((1 : ℕ) : ℝ) N (i21_38 x) = compl38 ((1 : ℕ) : ℝ) N (i21_38 x) :=
    (compl38_apply _ _ _).symm
  rw [hc]
  exact le_trans (tailN1 N x) (mul_le_mul_of_nonneg_left hx (inv_nonneg.2 (japaneseBracket_pos _).le))

end NlsGge.ClaudeH1.R117
