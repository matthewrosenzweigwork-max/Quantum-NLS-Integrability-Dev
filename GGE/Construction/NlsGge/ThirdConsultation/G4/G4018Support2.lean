import Mathlib
                                                        
                                                                                                
                                                                                
                                                                                                 
                                                                                                     
set_option autoImplicit false

namespace NlsGge.G4018Support

theorem summable_one_div_sq_int : Summable (fun j : ℤ => 1 / (j : ℝ) ^ 2) :=
  Real.summable_one_div_int_pow.mpr (by norm_num)

theorem sum_shift_sq_le (n : ℤ) (u : Finset ℤ) :
    ∑ m ∈ u, 1 / ((m - n : ℤ) : ℝ) ^ 2 ≤ ∑' j : ℤ, 1 / (j : ℝ) ^ 2 := by
  have hinj : Set.InjOn (fun m : ℤ => m - n) (u : Set ℤ) := by
    intro a _ b _ h
    simpa using h
  have hsum : ∑ m ∈ u, 1 / ((m - n : ℤ) : ℝ) ^ 2 =
      ∑ j ∈ u.image (fun m : ℤ => m - n), 1 / (j : ℝ) ^ 2 := by
    rw [Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
  rw [hsum]
  exact summable_one_div_sq_int.sum_le_tsum _ (fun j _ => by positivity)

theorem sum_mul_inv_abs_le (n : ℤ) (u : Finset ℤ) (d : ℤ → ℝ) (hd : ∀ m, 0 ≤ d m) (K S : ℝ)
    (hK : ∑ m ∈ u, d m ^ 2 ≤ K) (hS : ∑ m ∈ u, 1 / ((m - n : ℤ) : ℝ) ^ 2 ≤ S) (hK0 : 0 ≤ K) :
    ∑ m ∈ u, d m * (1 / |((m - n : ℤ) : ℝ)|) ≤ Real.sqrt K * Real.sqrt S := by
  have hsq : ∀ m : ℤ, (1 / |((m - n : ℤ) : ℝ)|) ^ 2 = 1 / ((m - n : ℤ) : ℝ) ^ 2 := by
    intro m
    rw [div_pow, one_pow, sq_abs]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt u d (fun m => 1 / |((m - n : ℤ) : ℝ)|)
  have h1 : Real.sqrt (∑ m ∈ u, d m ^ 2) ≤ Real.sqrt K := Real.sqrt_le_sqrt hK
  have h2 : Real.sqrt (∑ m ∈ u, (1 / |((m - n : ℤ) : ℝ)|) ^ 2) ≤ Real.sqrt S := by
    apply Real.sqrt_le_sqrt
    simpa only [hsq] using hS
  calc ∑ m ∈ u, d m * (1 / |((m - n : ℤ) : ℝ)|)
      ≤ Real.sqrt (∑ m ∈ u, d m ^ 2) * Real.sqrt (∑ m ∈ u, (1 / |((m - n : ℤ) : ℝ)|) ^ 2) := hcs
    _ ≤ Real.sqrt K * Real.sqrt S :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end NlsGge.G4018Support
