import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Host

                                                                                                                    
                                                                                                                          
                                      
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem one_le_indexWeight (n : ℤ) : 1 ≤ indexWeight n := by
  unfold indexWeight
  rw [Real.one_le_sqrt]
  nlinarith [sq_nonneg (n : ℝ)]

theorem indexWeight_pos (n : ℤ) : 0 < indexWeight n :=
  lt_of_lt_of_le one_pos (one_le_indexWeight n)

theorem indexValue_pos (n : ℤ) : 0 < indexValue n := indexWeight_pos n

/-- A square-summable sequence modified on a finite set is square summable. -/
theorem squareSummable_of_finite_support (e : ℤ → ℂ) (F : Finset ℤ)
    (he : ∀ n, n ∉ F → e n = 0) : SquareSummable e := by
  unfold SquareSummable
  apply summable_of_ne_finset_zero (s := F)
  intro n hn
  simp [he n hn]

theorem SquareSummable.add {e e' : ℤ → ℂ} (h : SquareSummable e) (h' : SquareSummable e') :
    SquareSummable (fun n => e n + e' n) := by
  unfold SquareSummable at *
  refine Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_) ((h.add h').mul_left 2)
  have := norm_add_le (e n) (e' n)
  have h1 : ‖e n + e' n‖ ^ 2 ≤ (‖e n‖ + ‖e' n‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) this 2
  nlinarith [sq_nonneg (‖e n‖ - ‖e' n‖)]

/-- Finite-change algebra (Pro round 13, section 4). -/
theorem finite_change_expansion (J : ℤ → ℝ) (hJ : ∀ n, 0 < J n)
    (L r r' : ℤ → ℂ) (F : Finset ℤ) (hF : ∀ n, n ∉ F → r' n = r n)
    (e : ℤ → ℂ) (he : SquareSummable e)
    (hr : ∀ n, r n = L n + e n / (J n : ℂ)) :
    ∃ e' : ℤ → ℂ, SquareSummable e' ∧ ∀ n, r' n = L n + e' n / (J n : ℂ) := by
  refine ⟨fun n => e n + (J n : ℂ) * (r' n - r n), ?_, ?_⟩
  · refine he.add (squareSummable_of_finite_support _ F ?_)
    intro n hn
    simp [hF n hn]
  · intro n
    have hJn : (J n : ℂ) ≠ 0 := by exact_mod_cast (hJ n).ne'
    show r' n = L n + (e n + (J n : ℂ) * (r' n - r n)) / (J n : ℂ)
    rw [add_div, mul_div_cancel_left₀ _ hJn]
    have := hr n
    linear_combination this

/-- The zero-sample set of a sequence with `‖xi n - n π‖ ≤ a / indexWeight n` is finite. -/
theorem zero_samples_finite (xi : ℤ → ℂ) (a : ℝ)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) :
    {n : ℤ | xi n = 0}.Finite := by
  apply (Set.finite_Icc (-⌈a / Real.pi⌉) ⌈a / Real.pi⌉).subset
  intro n hn
  have hn0 : xi n = 0 := hn
  have h1 := hxi n
  rw [hn0, zero_sub, norm_neg] at h1
  have hw := one_le_indexWeight n
  have hwp := indexWeight_pos n
  have ha : 0 ≤ a := by
    by_contra hneg
    have : a / indexWeight n < 0 := div_neg_of_neg_of_pos (not_le.mp hneg) hwp
    linarith [norm_nonneg ((n : ℂ) * (Real.pi : ℂ))]
  have h2 : a / indexWeight n ≤ a / 1 := div_le_div_of_nonneg_left ha one_pos hw
  have h3 : ‖(n : ℂ) * (Real.pi : ℂ)‖ = |(n : ℝ)| * Real.pi := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [h3] at h1
  have h4 : |(n : ℝ)| ≤ a / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]; linarith
  have h5 : |(n : ℝ)| ≤ (⌈a / Real.pi⌉ : ℝ) := h4.trans (Int.le_ceil _)
  rw [abs_le] at h5
  constructor
  · have := h5.1
    exact_mod_cast (by linarith : (-(⌈a / Real.pi⌉ : ℝ)) ≤ n)
  · exact_mod_cast h5.2

end
end NlsGge.ThirdConsultation.KSPS
