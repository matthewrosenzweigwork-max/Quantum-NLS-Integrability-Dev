import Mathlib
import NlsGge.Sobolev.SourceWeighted
import NlsGge.Measure.FourierGaussian
import NlsGge.Weights.LowerGrowth

                                                                                                                      
                                                                            
                                                                                                                  
                                                                                                          
                                                                                                    

set_option autoImplicit false

namespace NlsGge.Atomic.I002

open NlsGge.Pilot

theorem i002 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    (∀ r : ℝ, Summable (NlsGge.weightTerm c.val r) ∧
      0 < c.val 0 ∧ c.val 0 ≤ NlsGge.Weights.weight c.val r ∧
      NlsGge.Weights.weight c.val (-r) = NlsGge.Weights.weight c.val r ∧
      ∀ j : ℕ, NlsGge.weightTerm c.val r j ≤ NlsGge.Weights.weight c.val r) ∧
    (∀ m : ℕ, Summable (fun n : ℤ =>
      (1 + (n : ℝ) ^ 2) ^ m / NlsGge.Measure.fullWeightRate c.val n)) := by
  obtain ⟨hl, _hlu, hbd⟩ := c.2
  have hbound : ∀ j : ℕ, lower ≤ c.val j := fun j => (hbd j).1
  have hupper : ∀ j : ℕ, c.val j ≤ upper := fun j => (hbd j).2
  have hnn : ∀ r : ℝ, ∀ j : ℕ, 0 ≤ NlsGge.weightTerm c.val r j := fun r j =>
    NlsGge.Weights.weightTerm_nonneg lower c.val hl hbound r j
  have hle : ∀ r : ℝ, ∀ j : ℕ,
      NlsGge.weightTerm c.val r j ≤ NlsGge.Weights.weight c.val r := by
    intro r j
    exact (NlsGge.Weights.weightTerm_summable lower upper c.val hl hbound hupper r).le_tsum j
      (fun k _ => hnn r k)
  have hcle : ∀ r : ℝ, c.val 0 ≤ NlsGge.Weights.weight c.val r := by
    intro r
    have h := hle r 0
    rwa [NlsGge.Weights.weightTerm_zero_index] at h
  -- lower growth of the full rate, for |n| >= 3
  have hgrow : ∀ n : ℤ, 3 ≤ |n| →
      lower * Real.exp (Real.log 16 / 4 * Real.sqrt (2 * Real.pi * |(n : ℝ)|)) ≤
        NlsGge.Measure.fullWeightRate c.val n := by
    intro n hn
    have hn' : (3 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast hn
    have hpi := Real.pi_gt_three
    rcases le_total 0 n with h0 | h0
    · have h0' : (0 : ℝ) ≤ n := by exact_mod_cast h0
      have habs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg h0'
      rw [habs] at hn' ⊢
      have hr : (16 : ℝ) ≤ 2 * Real.pi * n := by nlinarith
      have h := NlsGge.Weights.weight_lower_growth_explicit lower upper c.val hl hbound hupper
        (2 * Real.pi * n) hr
      unfold NlsGge.Measure.fullWeightRate
      exact h
    · have h0' : (n : ℝ) ≤ 0 := by exact_mod_cast h0
      have habs : |(n : ℝ)| = -(n : ℝ) := abs_of_nonpos h0'
      rw [habs] at hn' ⊢
      have hr : (16 : ℝ) ≤ 2 * Real.pi * (-(n : ℝ)) := by nlinarith
      have h := NlsGge.Weights.weight_lower_growth_explicit lower upper c.val hl hbound hupper
        (2 * Real.pi * (-(n : ℝ))) hr
      have e : NlsGge.Weights.weight c.val (2 * Real.pi * (n : ℝ)) =
          NlsGge.Weights.weight c.val (2 * Real.pi * (-(n : ℝ))) := by
        rw [← NlsGge.Weights.weight_even c.val (2 * Real.pi * (-(n : ℝ)))]
        congr 1
        ring
      unfold NlsGge.Measure.fullWeightRate
      rw [e]
      exact h
  refine ⟨fun r => ⟨NlsGge.Weights.weightTerm_summable lower upper c.val hl hbound hupper r,
    lt_of_lt_of_le hl (hbound 0), hcle r, NlsGge.Weights.weight_even c.val r, fun j => hle r j⟩, ?_⟩
  intro m
  -- constants
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = Real.log 16 / 4 := ⟨_, rfl⟩
  have hκ : 0 < κ := by
    rw [hκdef]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  obtain ⟨D, hD⟩ : ∃ D : ℝ,
      D = lower * κ ^ (4 * m + 4) * (2 * Real.pi) ^ (2 * m + 2) / ((4 * m + 4).factorial : ℝ) :=
    ⟨_, rfl⟩
  have hDpos : 0 < D := by
    rw [hD]
    exact div_pos (mul_pos (mul_pos hl (pow_pos hκ _)) (pow_pos (by positivity) _))
      (by positivity)
  -- lower bound by D (n^2)^(m+1) for |n| >= 3
  have hbig : ∀ n : ℤ, 3 ≤ |n| → D * ((n : ℝ) ^ 2) ^ (m + 1) ≤
      NlsGge.Measure.fullWeightRate c.val n := by
    intro n hn
    have hpos_s : 0 ≤ 2 * Real.pi * |(n : ℝ)| := by positivity
    have hsq : Real.sqrt (2 * Real.pi * |(n : ℝ)|) ^ 2 = 2 * Real.pi * |(n : ℝ)| :=
      Real.sq_sqrt hpos_s
    have hexp := NlsGge.Weights.expSeries_term_le
      (κ * Real.sqrt (2 * Real.pi * |(n : ℝ)|)) (by positivity) (4 * m + 4)
    have key2 : (κ * Real.sqrt (2 * Real.pi * |(n : ℝ)|)) ^ (4 * m + 4) =
        κ ^ (4 * m + 4) * (2 * Real.pi * |(n : ℝ)|) ^ (2 * m + 2) := by
      rw [mul_pow, show Real.sqrt (2 * Real.pi * |(n : ℝ)|) ^ (4 * m + 4) =
        (Real.sqrt (2 * Real.pi * |(n : ℝ)|) ^ 2) ^ (2 * m + 2) by ring, hsq]
    have key3 : (2 * Real.pi * |(n : ℝ)|) ^ (2 * m + 2) =
        (2 * Real.pi) ^ (2 * m + 2) * ((n : ℝ) ^ 2) ^ (m + 1) := by
      rw [mul_pow]
      congr 1
      rw [← sq_abs (n : ℝ)]
      ring
    have h2 : D * ((n : ℝ) ^ 2) ^ (m + 1) =
        lower * ((κ * Real.sqrt (2 * Real.pi * |(n : ℝ)|)) ^ (4 * m + 4) /
          ((4 * m + 4).factorial : ℝ)) := by
      rw [key2, key3, hD]
      ring
    have hg := hgrow n hn
    rw [← hκdef] at hg
    calc D * ((n : ℝ) ^ 2) ^ (m + 1)
        = lower * ((κ * Real.sqrt (2 * Real.pi * |(n : ℝ)|)) ^ (4 * m + 4) /
          ((4 * m + 4).factorial : ℝ)) := h2
      _ ≤ lower * Real.exp (κ * Real.sqrt (2 * Real.pi * |(n : ℝ)|)) :=
          mul_le_mul_of_nonneg_left hexp hl.le
      _ ≤ NlsGge.Measure.fullWeightRate c.val n := hg
  -- termwise bound by a constant times 1 / n^2
  have hterm : ∀ n : ℤ, 3 ≤ |n| →
      ‖(1 + (n : ℝ) ^ 2) ^ m / NlsGge.Measure.fullWeightRate c.val n‖ ≤
        (2 ^ m / D) * (1 / (n : ℝ) ^ 2) := by
    intro n hn
    have h3 : (3 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hn
    have hn2 : (9 : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith [sq_abs (n : ℝ), abs_nonneg (n : ℝ)]
    have hn0 : (n : ℝ) ^ 2 ≠ 0 := by positivity
    have hWpos : 0 < NlsGge.Measure.fullWeightRate c.val n :=
      lt_of_lt_of_le (mul_pos hl (Real.exp_pos _)) (hgrow n hn)
    rw [Real.norm_of_nonneg (div_nonneg (by positivity) hWpos.le)]
    have hbg := hbig n hn
    have hcpos : 0 < D * ((n : ℝ) ^ 2) ^ (m + 1) := mul_pos hDpos (by positivity)
    have hnz : (n : ℝ) ≠ 0 := by
      intro h; rw [h] at hn2; norm_num at hn2
    calc (1 + (n : ℝ) ^ 2) ^ m / NlsGge.Measure.fullWeightRate c.val n
        ≤ (1 + (n : ℝ) ^ 2) ^ m / (D * ((n : ℝ) ^ 2) ^ (m + 1)) :=
          div_le_div_of_nonneg_left (by positivity) hcpos hbg
      _ ≤ (2 * (n : ℝ) ^ 2) ^ m / (D * ((n : ℝ) ^ 2) ^ (m + 1)) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by nlinarith) m)
            hcpos.le
      _ = (2 ^ m / D) * (1 / (n : ℝ) ^ 2) := by
          rw [mul_pow, pow_succ]
          field_simp
          ring
  -- summability of the bound over the integers, eventually
  refine Summable.of_norm_bounded_eventually
    (((Real.summable_one_div_int_pow (p := 2)).mpr one_lt_two).mul_left (2 ^ m / D)) ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_Icc (-2 : ℤ) 2).subset ?_
  intro n hn
  by_contra hc
  simp only [Set.mem_Icc, not_and_or, not_le] at hc
  have h3 : 3 ≤ |n| := by
    rcases abs_cases n with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> omega
  exact hn (hterm n h3)

#print axioms NlsGge.Atomic.I002.i002

end NlsGge.Atomic.I002
