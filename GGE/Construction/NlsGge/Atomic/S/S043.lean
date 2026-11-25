import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualSchurGapEnergyLower38V1

                                                                                                            
                                                                                                                              
                                                                                                       
                                                                                                                                  
                                         
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem schurRho_product_bound (C : ℝ) (hC : 0 ≤ C) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (M N : ℕ),
      R ^ 6 ≤ (M : ℝ) →
      (∏ n ∈ normalizerHigh M N, (rhoAt C R n)⁻¹) ≤ Real.exp L := by
  refine ⟨8 * C, by positivity, ?_⟩
  intro R hR M N hMR
  have hR6 : 1 ≤ R ^ 6 := one_le_pow₀ hR
  have hM1 : 1 ≤ M := by
    have : (0 : ℝ) < (M : ℝ) := by linarith
    exact_mod_cast this
  set f : ℤ → ℝ := fun n => if M < n.natAbs then
      R ^ 3 * |(n : ℝ)| ^ (-(3 / 2) : ℝ) + R ^ 4 / (n : ℝ) ^ 2 else 0 with hf
  obtain ⟨hsum, htail⟩ := rhoTail_real38 R (by linarith) M hM1
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n; simp only [hf]; split_ifs <;> positivity
  have hprod : ∏ n ∈ normalizerHigh M N, (rhoAt C R n)⁻¹ =
      Real.exp (C * ∑ n ∈ normalizerHigh M N, f n) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun n hn => ?_
    have hn' : M < n.natAbs := (Finset.mem_filter.mp hn).2
    simp only [hf, if_pos hn']
    rw [rhoAt, ← Real.exp_neg]
    congr 1
    rw [Real.rpow_neg (abs_nonneg _), sq_abs]
    ring
  rw [hprod]
  apply Real.exp_le_exp.mpr
  have hfin : ∑ n ∈ normalizerHigh M N, f n ≤ ∑' n : ℤ, f n :=
    hsum.sum_le_tsum _ (fun n _ => hf0 n)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hR0 : 0 < R := by linarith
  have h1 : R ^ 3 * (M : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 := by
    have hsq : R ^ 3 ≤ Real.sqrt M := by
      rw [show R ^ 3 = Real.sqrt ((R ^ 3) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt; nlinarith
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hMpos.le,
      ← Real.sqrt_eq_rpow]
    rw [mul_inv_le_iff₀ (Real.sqrt_pos.mpr hMpos)]
    linarith
  have h2 : R ^ 4 / M ≤ 1 := by
    rw [div_le_one hMpos]
    have : R ^ 4 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
    linarith
  calc C * ∑ n ∈ normalizerHigh M N, f n ≤ C * ∑' n : ℤ, f n :=
        mul_le_mul_of_nonneg_left hfin hC
    _ ≤ C * (4 * (R ^ 3 * (M : ℝ) ^ (-1 / 2 : ℝ) + R ^ 4 / M)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        simpa [hf] using htail
    _ ≤ C * (4 * (1 + 1)) := by gcongr
    _ = 8 * C := by ring

end NlsGge.ThirdConsultation.S

end
