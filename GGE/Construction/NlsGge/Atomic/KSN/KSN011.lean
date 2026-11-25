                                                                                 
                                                                                   
                                                                         
                                                                         
                                                                     

         
                                                     
                                                                                        
                                                                   
                                                                                         
                                                                      
                                                                                          
                                        
                                                                                          
                                                                                            
                                                                                 
                                                                      

import NlsGge.Definitions.PilotInterfaces

set_option autoImplicit false

open scoped BigOperators
open Filter Topology

namespace NlsGge.Atomic.KSN011

open NlsGge.Pilot

lemma br_pos (k : ℤ) : 0 < japaneseBracket k := by
  unfold japaneseBracket
  exact Real.sqrt_pos.mpr (by positivity)

lemma br_sq (k : ℤ) : japaneseBracket k ^ 2 = 1 + (k : ℝ) ^ 2 := by
  unfold japaneseBracket
  exact Real.sq_sqrt (by positivity)

lemma br_pointwise (n k : ℤ) :
    japaneseBracket n ^ 2 ≤ 2 * japaneseBracket k ^ 2 + 2 * ((k : ℝ) - n) ^ 2 := by
  rw [br_sq, br_sq]
  nlinarith [sq_nonneg (2 * (k : ℝ) - n)]

/-- Pointwise kernel bound: 1/(x^2 y^2) ≤ (4/N)(1/y^2 + 1/x^2) when N ≤ 2x^2 + 2y^2. -/
lemma kernel_sq (x y N : ℝ) (hx : 0 < x) (hy : 0 < y) (hN : 0 < N)
    (h : N ≤ 2 * x ^ 2 + 2 * y ^ 2) :
    1 / (x ^ 2 * y ^ 2) ≤ 4 / N * (1 / y ^ 2 + 1 / x ^ 2) := by
  have hx2 : 0 < x ^ 2 := by positivity
  have hy2 : 0 < y ^ 2 := by positivity
  by_cases h1 : N ≤ 4 * x ^ 2
  · have h2 : 1 / x ^ 2 ≤ 4 / N := by
      rw [div_le_div_iff₀ hx2 hN]
      linarith
    have h3 : 1 / (x ^ 2 * y ^ 2) = (1 / x ^ 2) * (1 / y ^ 2) := by
      rw [one_div_mul_one_div]
    rw [h3]
    have h4 : 0 ≤ 1 / y ^ 2 := by positivity
    have h5 : 0 ≤ 1 / x ^ 2 := by positivity
    calc (1 / x ^ 2) * (1 / y ^ 2) ≤ (4 / N) * (1 / y ^ 2) :=
          mul_le_mul_of_nonneg_right h2 h4
      _ ≤ 4 / N * (1 / y ^ 2 + 1 / x ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · by_cases h2 : N ≤ 4 * y ^ 2
    · have h2' : 1 / y ^ 2 ≤ 4 / N := by
        rw [div_le_div_iff₀ hy2 hN]
        linarith
      have h3 : 1 / (x ^ 2 * y ^ 2) = (1 / y ^ 2) * (1 / x ^ 2) := by
        rw [one_div_mul_one_div, mul_comm]
      rw [h3]
      have h4 : 0 ≤ 1 / x ^ 2 := by positivity
      have h5 : 0 ≤ 1 / y ^ 2 := by positivity
      calc (1 / y ^ 2) * (1 / x ^ 2) ≤ (4 / N) * (1 / x ^ 2) :=
            mul_le_mul_of_nonneg_right h2' h4
        _ ≤ 4 / N * (1 / y ^ 2 + 1 / x ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · exfalso
      push_neg at h1 h2
      linarith

/-- Pointwise bound of the squared weight g_n(k) = 1/(⟨k⟩|k−n|) (0 at k = n). -/
lemma sq_term_bound (n k : ℤ) :
    (if k = n then (0 : ℝ) else 1 / (japaneseBracket k * |(k : ℝ) - n|)) ^ 2 ≤
      4 / japaneseBracket n ^ 2 * (1 / ((k : ℝ) - n) ^ 2 + 1 / japaneseBracket k ^ 2) := by
  by_cases hkn : k = n
  · subst hkn
    rw [if_pos rfl, zero_pow two_ne_zero]
    positivity
  · rw [if_neg hkn]
    have hx := br_pos k
    have hy : 0 < |(k : ℝ) - n| := by
      apply abs_pos.mpr
      intro h0
      apply hkn
      exact_mod_cast sub_eq_zero.mp h0
    have hN : 0 < japaneseBracket n ^ 2 := by
      have := br_pos n
      positivity
    have key := kernel_sq (japaneseBracket k) |(k : ℝ) - n| (japaneseBracket n ^ 2) hx hy hN
      (by rw [sq_abs]; exact br_pointwise n k)
    rw [sq_abs] at key
    rw [div_pow, one_pow, mul_pow, sq_abs]
    exact key

/-- Shifted reciprocal squares are summable, and their total is the same for every shift. -/
lemma summable_inv_sq_shift (n : ℤ) :
    Summable (fun k : ℤ => 1 / ((k : ℝ) - n) ^ 2) := by
  have hsq1 : Summable (fun m : ℤ => 1 / (m : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have h : Summable (fun k : ℤ => 1 / (((k - n) : ℤ) : ℝ) ^ 2) :=
    hsq1.comp_injective sub_left_injective
  simpa only [Int.cast_sub] using h

/-- Summability of the square of the weight 1/⟨k⟩. -/
lemma summable_inv_br_sq :
    Summable (fun k : ℤ => 1 / japaneseBracket k ^ 2) := by
  have hsq1 : Summable (fun m : ℤ => 1 / (m : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hfin : Summable (fun k : ℤ => if k = 0 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (fun b hb => by
      rw [Finset.mem_singleton] at hb
      rw [if_neg hb])
  refine Summable.of_nonneg_of_le (fun k => by
      have := br_pos k
      positivity) (fun k => ?_) (hsq1.add hfin)
  rw [br_sq]
  by_cases hk : k = 0
  · subst hk
    norm_num
  · have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by
      have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    rw [if_neg hk, add_zero]
    apply one_div_le_one_div_of_le hk2
    linarith

/-- The total weight bound: ⟨n⟩^2 Σ_k g_n(k)^2 ≤ 4(T1 + T2). -/
lemma weight_bound (n : ℤ) :
    japaneseBracket n ^ 2 *
      (∑' k : ℤ, (if k = n then (0 : ℝ) else 1 / (japaneseBracket k * |(k : ℝ) - n|)) ^ 2) ≤
      4 * ((∑' m : ℤ, 1 / (m : ℝ) ^ 2) + ∑' k : ℤ, 1 / japaneseBracket k ^ 2) := by
  have hsq1 : Summable (fun m : ℤ => 1 / (m : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hshift : ∑' k : ℤ, 1 / ((k : ℝ) - n) ^ 2 = ∑' m : ℤ, 1 / (m : ℝ) ^ 2 := by
    have e : (fun k : ℤ => 1 / ((k : ℝ) - n) ^ 2) =
        fun k => (fun m : ℤ => 1 / (m : ℝ) ^ 2) ((Equiv.subRight n) k) := by
      funext k
      simp only [Equiv.subRight_apply]
      push_cast
      rfl
    rw [e, Equiv.tsum_eq (Equiv.subRight n) (fun m : ℤ => 1 / (m : ℝ) ^ 2)]
  have hRHS : Summable (fun k : ℤ =>
      4 / japaneseBracket n ^ 2 * (1 / ((k : ℝ) - n) ^ 2 + 1 / japaneseBracket k ^ 2)) :=
    ((summable_inv_sq_shift n).add summable_inv_br_sq).mul_left _
  have hLHS : Summable (fun k : ℤ =>
      (if k = n then (0 : ℝ) else 1 / (japaneseBracket k * |(k : ℝ) - n|)) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => by
        by_cases hk : k = n
        · rw [if_pos hk]; positivity
        · rw [if_neg hk]; positivity)
      (fun k => sq_term_bound n k) hRHS
  have hbound : ∑' k : ℤ, (if k = n then (0 : ℝ) else 1 / (japaneseBracket k * |(k : ℝ) - n|)) ^ 2 ≤
      4 / japaneseBracket n ^ 2 *
        ((∑' m : ℤ, 1 / (m : ℝ) ^ 2) + ∑' k : ℤ, 1 / japaneseBracket k ^ 2) := by
    calc ∑' k : ℤ, (if k = n then (0 : ℝ) else 1 / (japaneseBracket k * |(k : ℝ) - n|)) ^ 2
        ≤ ∑' k : ℤ, 4 / japaneseBracket n ^ 2 *
            (1 / ((k : ℝ) - n) ^ 2 + 1 / japaneseBracket k ^ 2) :=
          hLHS.tsum_le_tsum (fun k => sq_term_bound n k) hRHS
      _ = 4 / japaneseBracket n ^ 2 *
            ((∑' m : ℤ, 1 / (m : ℝ) ^ 2) + ∑' k : ℤ, 1 / japaneseBracket k ^ 2) := by
          rw [tsum_mul_left, Summable.tsum_add (summable_inv_sq_shift n) summable_inv_br_sq, hshift]
  have hpos : 0 < japaneseBracket n ^ 2 := by
    have := br_pos n
    positivity
  have hbr0 : japaneseBracket n ≠ 0 := (br_pos n).ne'
  calc japaneseBracket n ^ 2 *
        (∑' k : ℤ, (if k = n then (0 : ℝ) else 1 / (japaneseBracket k * |(k : ℝ) - n|)) ^ 2)
      ≤ japaneseBracket n ^ 2 * (4 / japaneseBracket n ^ 2 *
          ((∑' m : ℤ, 1 / (m : ℝ) ^ 2) + ∑' k : ℤ, 1 / japaneseBracket k ^ 2)) :=
        mul_le_mul_of_nonneg_left hbound hpos.le
    _ = 4 * ((∑' m : ℤ, 1 / (m : ℝ) ^ 2) + ∑' k : ℤ, 1 / japaneseBracket k ^ 2) := by
        field_simp

/-- Main statement: Cauchy–Schwarz (Hölder with p = q = 2) plus the weight bound. -/
theorem ksn011_statement :
    ∃ C : ℝ, ∀ a : lp (fun _ : ℤ => ℂ) 2, ∀ n : ℤ,
      Summable (fun k : ℤ => if k = n then (0 : ℝ) else
        ‖a k‖ / (japaneseBracket k * |(k : ℝ) - (n : ℝ)|)) ∧
      japaneseBracket n *
        (∑' k : ℤ, if k = n then (0 : ℝ) else
          ‖a k‖ / (japaneseBracket k * |(k : ℝ) - (n : ℝ)|)) ≤
        C * ‖a‖ := by
  refine ⟨Real.sqrt (4 * ((∑' m : ℤ, 1 / (m : ℝ) ^ 2) + ∑' k : ℤ, 1 / japaneseBracket k ^ 2)),
    fun a n => ?_⟩
  set g : ℤ → ℝ := fun k => if k = n then (0 : ℝ) else 1 / (japaneseBracket k * |(k : ℝ) - n|)
    with hg_def
  have hfun : (fun k : ℤ => if k = n then (0 : ℝ) else ‖a k‖ / (japaneseBracket k * |(k : ℝ) - n|))
      = fun k => ‖a k‖ * g k := by
    funext k
    by_cases hk : k = n
    · rw [hg_def]
      simp only [if_pos hk, mul_zero]
    · rw [hg_def]
      simp only [if_neg hk]
      rw [div_eq_mul_one_div]
  have hg_nonneg : ∀ k, 0 ≤ g k := by
    intro k
    rw [hg_def]
    by_cases hk : k = n
    · simp only [if_pos hk, le_refl]
    · simp only [if_neg hk]
      have := br_pos k
      positivity
  have hf_nonneg : ∀ k : ℤ, 0 ≤ ‖a k‖ := fun k => norm_nonneg _
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have ha2 : Summable (fun k : ℤ => ‖a k‖ ^ (2 : ℝ)) := by
    have h := Memℓp.summable hp (lp.memℓp a)
    simpa using h
  have hg2 : Summable (fun k : ℤ => g k ^ (2 : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (hg_nonneg k) _) (fun k => ?_)
      ((((summable_inv_sq_shift n).add summable_inv_br_sq).mul_left
        (4 / japaneseBracket n ^ 2)))
    rw [Real.rpow_two]
    exact sq_term_bound n k
  have hholder := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two hf_nonneg hg_nonneg ha2 hg2
  obtain ⟨hsum_fg, hineq⟩ := hholder
  have e2 : (2 : ENNReal).toReal = 2 := by norm_num
  have hnorm : ‖a‖ = (∑' k : ℤ, ‖a k‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    have h := lp.norm_eq_tsum_rpow hp a
    rw [e2] at h
    exact h
  have hSw : ∑' k : ℤ, g k ^ (2 : ℝ) =
      ∑' k : ℤ, (if k = n then (0 : ℝ) else 1 / (japaneseBracket k * |(k : ℝ) - n|)) ^ 2 :=
    tsum_congr (fun k => Real.rpow_two (g k))
  have hw := weight_bound n
  rw [← hSw] at hw
  rw [← hnorm] at hineq
  rw [← Real.sqrt_eq_rpow] at hineq
  set S : ℝ := ∑' k : ℤ, g k ^ (2 : ℝ) with hS_def
  have hsqrt : japaneseBracket n * Real.sqrt S ≤
      Real.sqrt (4 * ((∑' m : ℤ, 1 / (m : ℝ) ^ 2) + ∑' k : ℤ, 1 / japaneseBracket k ^ 2)) := by
    calc japaneseBracket n * Real.sqrt S
        = Real.sqrt (japaneseBracket n ^ 2) * Real.sqrt S := by
          rw [Real.sqrt_sq (le_of_lt (br_pos n))]
      _ = Real.sqrt (japaneseBracket n ^ 2 * S) := (Real.sqrt_mul (sq_nonneg _) S).symm
      _ ≤ Real.sqrt (4 * ((∑' m : ℤ, 1 / (m : ℝ) ^ 2) + ∑' k : ℤ, 1 / japaneseBracket k ^ 2)) :=
          Real.sqrt_le_sqrt hw
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hsum_fg
  · rw [hfun]
    calc japaneseBracket n * (∑' k : ℤ, ‖a k‖ * g k)
        ≤ japaneseBracket n * (‖a‖ * Real.sqrt S) :=
          mul_le_mul_of_nonneg_left hineq (le_of_lt (br_pos n))
      _ = ‖a‖ * (japaneseBracket n * Real.sqrt S) := by ring
      _ ≤ ‖a‖ * Real.sqrt (4 * ((∑' m : ℤ, 1 / (m : ℝ) ^ 2) + ∑' k : ℤ, 1 / japaneseBracket k ^ 2)) :=
          mul_le_mul_of_nonneg_left hsqrt (norm_nonneg _)
      _ = Real.sqrt (4 * ((∑' m : ℤ, 1 / (m : ℝ) ^ 2) + ∑' k : ℤ, 1 / japaneseBracket k ^ 2)) * ‖a‖ :=
          mul_comm _ _

end NlsGge.Atomic.KSN011
