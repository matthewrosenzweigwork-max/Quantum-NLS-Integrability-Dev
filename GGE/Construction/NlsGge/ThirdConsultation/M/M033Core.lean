import Mathlib
import NlsGge.Atomic.M.M054

   
                                                                                      

                                                                                                         
                                                                        
                                                                                                   
                                                                                                    
                                                                  
                                                                                    
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M033Core

/-- A point of `[lo, hi]` is as close to `c` as both endpoints. -/
theorem abs_sub_le_of_mem_Icc {lo hi ζ c r : ℝ} (hζ : ζ ∈ Set.Icc lo hi)
    (hlo : |lo - c| ≤ r) (hhi : |hi - c| ≤ r) : |ζ - c| ≤ r := by
  rw [abs_le] at hlo hhi ⊢
  exact ⟨by linarith [hζ.1, hlo.1], by linarith [hζ.2, hhi.2]⟩

/-- A point of `[lo, hi]` is bounded by a common bound of both endpoints. -/
theorem abs_le_of_mem_Icc {lo hi ζ B : ℝ} (hζ : ζ ∈ Set.Icc lo hi)
    (hlo : |lo| ≤ B) (hhi : |hi| ≤ B) : |ζ| ≤ B := by
  rw [abs_le] at hlo hhi ⊢
  exact ⟨by linarith [hζ.1, hlo.1], by linarith [hζ.2, hhi.2]⟩

/-- On a nonzero label, the M-031 localization radius is at most `3/8`. -/
theorem radius_le (n : ℤ) (hn : n ≠ 0) (Q : ℝ)
    (h : 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n) :
    Q ^ 2 / NlsGge.Atomic.M.M054.indexWeight n +
      Real.sqrt 2 * Q / NlsGge.Atomic.M.M054.indexWeight (2 * n) ≤ 3 / 8 := by
  unfold NlsGge.Atomic.M.M054.indexWeight at h ⊢
  have hk1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
  have h2n : |(((2 * n : ℤ)) : ℝ)| = 2 * |(n : ℝ)| := by
    push_cast; rw [abs_mul]; norm_num
  rw [h2n]
  have ha : (0 : ℝ) < 1 + |(n : ℝ)| := by positivity
  have hb : (0 : ℝ) < 1 + 2 * |(n : ℝ)| := by positivity
  have t1 : Q ^ 2 / (1 + |(n : ℝ)|) ≤ 1 / 8 := by
    rw [div_le_iff₀ ha]; linarith
  have t2 : Real.sqrt 2 * Q / (1 + 2 * |(n : ℝ)|) ≤ 1 / 4 := by
    rw [div_le_iff₀ hb]
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    by_contra hc
    rw [not_le] at hc
    have hprod := mul_lt_mul'' hc hc (by positivity) (by positivity)
    have e : (Real.sqrt 2 * Q) * (Real.sqrt 2 * Q) = 2 * Q ^ 2 := by
      rw [show (Real.sqrt 2 * Q) * (Real.sqrt 2 * Q) = (Real.sqrt 2 * Real.sqrt 2) * Q ^ 2 by ring, hs]
    rw [e] at hprod
    nlinarith [hk1]
  linarith

/-- High labels: `4ζ² ≤ (1+|2πn|)² ≤ 8ζ²` when `ζ` lies within `3/8` of `nπ`, `n ≠ 0`. -/
theorem high_core (n : ℤ) (hn : n ≠ 0) (ζ r : ℝ) (hr : r ≤ 3 / 8)
    (hζ : |ζ - (n : ℝ) * Real.pi| ≤ r) :
    4 * ζ ^ 2 ≤ (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 ∧
      (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 ≤ 8 * ζ ^ 2 := by
  have hk1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
  have hw : |2 * Real.pi * (n : ℝ)| = 2 * (Real.pi * |(n : ℝ)|) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]; ring
  have hc : |(n : ℝ) * Real.pi| = Real.pi * |(n : ℝ)| := by
    rw [abs_mul, abs_of_pos Real.pi_pos, mul_comm]
  have hpi := Real.pi_gt_three
  have hx3 : 3 ≤ Real.pi * |(n : ℝ)| := by
    have : Real.pi ≤ Real.pi * |(n : ℝ)| := le_mul_of_one_le_right Real.pi_pos.le hk1
    linarith
  have hup : |ζ| ≤ Real.pi * |(n : ℝ)| + 3 / 8 := by
    have := abs_sub_abs_le_abs_sub ζ ((n : ℝ) * Real.pi)
    rw [hc] at this; linarith
  have hlow : Real.pi * |(n : ℝ)| - 3 / 8 ≤ |ζ| := by
    have := abs_sub_abs_le_abs_sub ((n : ℝ) * Real.pi) ζ
    rw [hc, abs_sub_comm] at this; linarith
  rw [hw, ← sq_abs ζ]
  set x : ℝ := Real.pi * |(n : ℝ)| with hx
  set a : ℝ := |ζ| with ha
  have ha0 : 0 ≤ a := abs_nonneg ζ
  constructor
  · have h2 : 2 * a ≤ 1 + 2 * x := by linarith
    have hpos : 0 ≤ 1 + 2 * x + 2 * a := by linarith
    nlinarith [mul_nonneg (sub_nonneg.2 h2) hpos]
  · have hb : 0 ≤ x - 3 / 8 := by linarith
    have hsq : (x - 3 / 8) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hb hlow 2
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x) (by linarith : (0 : ℝ) ≤ x - 3)]

/-- Raise `4ζ² ≤ w² ≤ 8ζ²` to the power `m` and multiply by a nonnegative action. -/
theorem high_pow (m : ℕ) (ζ w I : ℝ) (hI : 0 ≤ I)
    (h1 : 4 * ζ ^ 2 ≤ w ^ 2) (h2 : w ^ 2 ≤ 8 * ζ ^ 2) :
    (2 : ℝ) ^ (-(m : ℤ)) * (w ^ m) ^ 2 * I ≤ (4 : ℝ) ^ m * (ζ ^ (2 * m) * I) ∧
      (4 : ℝ) ^ m * (ζ ^ (2 * m) * I) ≤ (w ^ m) ^ 2 * I := by
  have hA : 0 ≤ 4 * ζ ^ 2 := by positivity
  have e : (4 : ℝ) ^ m * (ζ ^ (2 * m) * I) = (4 * ζ ^ 2) ^ m * I := by
    rw [pow_mul, ← mul_assoc, ← mul_pow]
  have ew : (w ^ m) ^ 2 = (w ^ 2) ^ m := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [e, ew]
  constructor
  · have h8 : (w ^ 2) ^ m ≤ 2 ^ m * (4 * ζ ^ 2) ^ m := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) m
    rw [zpow_neg, zpow_natCast]
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    have hle : (2 ^ m)⁻¹ * (w ^ 2) ^ m ≤ (4 * ζ ^ 2) ^ m := by
      rw [inv_mul_le_iff₀ hp]; exact h8
    exact mul_le_mul_of_nonneg_right hle hI
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA h1 m) hI

/-- Low labels: `|ζ| ≤ 8πQ²` gives the source polynomial `(16π)^(2m) Q^(4m)`. -/
theorem low_core (m : ℕ) (ζ Q I : ℝ) (hI : 0 ≤ I)
    (hζ : |ζ| ≤ 8 * Real.pi * Q ^ 2) :
    (4 : ℝ) ^ m * (ζ ^ (2 * m) * I) ≤ (16 * Real.pi) ^ (2 * m) * Q ^ (4 * m) * I := by
  have h1 : 4 * ζ ^ 2 ≤ (16 * Real.pi) ^ 2 * Q ^ 4 := by
    have hsq := pow_le_pow_left₀ (abs_nonneg ζ) hζ 2
    rw [sq_abs] at hsq
    calc 4 * ζ ^ 2 ≤ 4 * (8 * Real.pi * Q ^ 2) ^ 2 := by linarith
      _ = (16 * Real.pi) ^ 2 * Q ^ 4 := by ring
  have e1 : (4 : ℝ) ^ m * (ζ ^ (2 * m) * I) = (4 * ζ ^ 2) ^ m * I := by
    rw [pow_mul ζ 2 m, ← mul_assoc, ← mul_pow]
  have e2 : (16 * Real.pi) ^ (2 * m) * Q ^ (4 * m) * I =
      ((16 * Real.pi) ^ 2 * Q ^ 4) ^ m * I := by
    rw [pow_mul (16 * Real.pi) 2 m, pow_mul Q 4 m, ← mul_pow]
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 m) hI

end NlsGge.ThirdConsultation.M033Core

end
