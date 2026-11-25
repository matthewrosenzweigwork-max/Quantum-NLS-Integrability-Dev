                                                                                                                                                                                                                                                        
                                                                             
import NlsGge.Hierarchy.RiccatiLocalRemainderPaperForm38
import NlsGge.Atomic.PhysicalSobolev
import Mathlib

                                           
                                        
                                                                                        
                                   
                                                                                           
                                                                                             
                                                                                                     
                                         
                                                           
                                                                                               
                                                                                                  
                                                                                                    

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.F

noncomputable def lowerChargeSymbol (m : ℕ) (n : ℤ) : ℝ :=
  (2 * Real.pi * (n : ℝ)) ^ (2 * (m - 1))

noncomputable def ratePrime (m : ℕ) (β : ℕ → ℝ) (δ : ℝ) (n : ℤ) : ℝ :=
  finiteHierarchyRate38 m β n - δ * lowerChargeSymbol m n

theorem rate_term_nonneg (M : ℕ) (β : ℕ → ℝ) (hβ : ∀ j ≤ M, 0 < β j) (r : ℝ) (j : ℕ)
    (hj : j ≤ M) : 0 ≤ β j * r ^ (2 * j) := by
  have h2 : 0 ≤ r ^ (2 * j) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg r) j
  exact mul_nonneg (hβ j hj).le h2

theorem rate_ge_term (M : ℕ) (β : ℕ → ℝ) (hβ : ∀ j ≤ M, 0 < β j) (r : ℝ) (j : ℕ)
    (hj : j ≤ M) : β j * r ^ (2 * j) ≤ finiteHierarchyW38 M β r := by
  unfold finiteHierarchyW38
  refine Finset.single_le_sum (f := fun i : ℕ => β i * r ^ (2 * i)) (fun i hi => ?_)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  exact rate_term_nonneg M β hβ r i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

theorem rate_pos (M : ℕ) (β : ℕ → ℝ) (hβ : ∀ j ≤ M, 0 < β j) (r : ℝ) :
    0 < finiteHierarchyW38 M β r := by
  have h := rate_ge_term M β hβ r 0 (Nat.zero_le M)
  rw [mul_zero, pow_zero, mul_one] at h
  exact lt_of_lt_of_le (hβ 0 (Nat.zero_le M)) h

/-- F-022, Pro's signature (STATEMENTS/F.md lines 489-500). -/
theorem f022 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) (δ : ℝ)
    (hδ : 0 < δ) (hδβ : δ < β (m - 1)) :
    δ / β (m - 1) < 1 ∧
    (∀ n : ℤ, 0 < ratePrime m β δ n ∧
      0 ≤ δ * lowerChargeSymbol m n / finiteHierarchyRate38 m β n ∧
      δ * lowerChargeSymbol m n / finiteHierarchyRate38 m β n ≤ δ / β (m - 1) ∧
      (1 - δ / β (m - 1)) * finiteHierarchyRate38 m β n ≤ ratePrime m β δ n) ∧
    Summable (fun n : ℤ => lowerChargeSymbol m n / finiteHierarchyRate38 m β n) := by
  have hbm1 : 0 < β (m - 1) := hβ (m - 1) (by omega)
  have hbm : 0 < β m := hβ m le_rfl
  have hratio : δ / β (m - 1) < 1 := (div_lt_one hbm1).2 hδβ
  have hL0 : ∀ n : ℤ, 0 ≤ lowerChargeSymbol m n := fun n => by
    unfold lowerChargeSymbol
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have hA : ∀ n : ℤ, β (m - 1) * lowerChargeSymbol m n ≤ finiteHierarchyRate38 m β n := by
    intro n
    exact rate_ge_term m β hβ (2 * Real.pi * (n : ℝ)) (m - 1) (by omega)
  have hR : ∀ n : ℤ, 0 < finiteHierarchyRate38 m β n := fun n => rate_pos m β hβ _
  have hC : ∀ n : ℤ, β m * (2 * Real.pi * (n : ℝ)) ^ (2 * m) ≤ finiteHierarchyRate38 m β n :=
    fun n => rate_ge_term m β hβ _ m le_rfl
  have hkey : ∀ n : ℤ, δ * lowerChargeSymbol m n ≤ δ / β (m - 1) * finiteHierarchyRate38 m β n := by
    intro n
    rw [div_mul_eq_mul_div, le_div_iff₀ hbm1]
    have := mul_le_mul_of_nonneg_left (hA n) hδ.le
    nlinarith
  have hpart : ∀ n : ℤ, (1 - δ / β (m - 1)) * finiteHierarchyRate38 m β n ≤
      ratePrime m β δ n := by
    intro n
    unfold ratePrime
    have h1 := hkey n
    have e : (1 - δ / β (m - 1)) * finiteHierarchyRate38 m β n =
        finiteHierarchyRate38 m β n - δ / β (m - 1) * finiteHierarchyRate38 m β n := by ring
    rw [e]
    linarith
  have hbound : ∀ n : ℤ, lowerChargeSymbol m n / finiteHierarchyRate38 m β n ≤
      (1 / (β m * (2 * Real.pi) ^ 2)) * (1 / (n : ℝ) ^ 2) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have hL : lowerChargeSymbol m 0 = 0 := by
        unfold lowerChargeSymbol
        rw [Int.cast_zero, mul_zero, zero_pow (show 2 * (m - 1) ≠ 0 by omega)]
      rw [hL, zero_div]
      simp
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hX : (2 * Real.pi * (n : ℝ)) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hn')
      have hXpos : 0 < (2 * Real.pi * (n : ℝ)) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hX)
      have hLeq : (2 * Real.pi * (n : ℝ)) ^ (2 * m) =
          lowerChargeSymbol m n * (2 * Real.pi * (n : ℝ)) ^ 2 := by
        unfold lowerChargeSymbol
        rw [← pow_add]
        congr 1
        omega
      have hRge := hC n
      rw [hLeq] at hRge
      have hβX : 0 < β m * (2 * Real.pi * (n : ℝ)) ^ 2 := mul_pos hbm hXpos
      have hsplit : 1 / (β m * (2 * Real.pi * (n : ℝ)) ^ 2) =
          (1 / (β m * (2 * Real.pi) ^ 2)) * (1 / (n : ℝ) ^ 2) := by
        rw [div_mul_div_comm, one_mul]
        congr 1
        ring
      rw [← hsplit, div_le_iff₀ (hR n), one_div_mul_eq_div, le_div_iff₀ hβX]
      nlinarith [hRge]
  refine ⟨hratio, fun n => ⟨?_, ?_, ?_, hpart n⟩, ?_⟩
  · have h1 : 0 < 1 - δ / β (m - 1) := by linarith
    have := mul_pos h1 (hR n)
    linarith [hpart n]
  · exact div_nonneg (mul_nonneg hδ.le (hL0 n)) (hR n).le
  · exact (div_le_iff₀ (hR n)).2 (hkey n)
  · exact Summable.of_nonneg_of_le (fun n => div_nonneg (hL0 n) (hR n).le) hbound
      (Summable.mul_left _ (Real.summable_one_div_int_pow.2 (by norm_num)))


end NlsGge.ThirdConsultation.F
