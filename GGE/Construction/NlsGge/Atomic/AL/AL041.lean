import Mathlib
import NlsGge.Hierarchy.ALQ4Ensemble38
                                                                                                                                                                                                                                                                
                                         

                                                                                            
                                                                                 
                                                                                     
                                                                                           
                                                                                                  
                                                                                     
                              

set_option autoImplicit false

open NlsGge.AblowitzLadik

namespace NlsGge.ThirdConsultation.AL

theorem alDelta38_iterate_smul {L : ℕ} [NeZero L] (c : ℂ) (m : ℕ) (Φ : ZMod L → ℂ) :
    (alDelta38^[m] (fun j => c * Φ j)) = fun j => c * (alDelta38^[m] Φ) j := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext i
    simp only [alDelta38, mul_sub]

theorem al041_dft (N : ℕ) (v : ZMod (2 * N + 1) → ℂ) (ν : ZMod (2 * N + 1)) :
    alDFT38 N v ν.valMinAbs = ZMod.dft (fun j => ((alh38 N : ℝ) : ℂ) * v j) ν := by
  have hC : ((alh38 N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (alh38_pos N).ne'
  have h := alDFT_eq_dft38 N (fun j => ((alh38 N : ℝ) : ℂ) * v j) ν
  simp only [inv_mul_cancel_left₀ hC] at h
  exact h

theorem al041_one (N : ℕ) (v : ZMod (2 * N + 1) → ℂ) :
    alh38 N * ∑ j, ‖v j‖ ^ 2 = ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ‖alDFT38 N v k‖ ^ 2 := by
  have hpos := alh38_pos N
  have hI : ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ‖alDFT38 N v k‖ ^ 2
      = ∑ ν : ZMod (2 * N + 1), ‖alDFT38 N v ν.valMinAbs‖ ^ 2 :=
    (sum_valMinAbs_eq_Icc38 N (fun ν => ‖alDFT38 N v ν‖ ^ 2)).symm
  rw [hI]
  simp only [al041_dft]
  rw [dft_parseval_norm38]
  have e : ∀ j, ‖((alh38 N : ℝ) : ℂ) * v j‖ ^ 2 = (alh38 N) ^ 2 * ‖v j‖ ^ 2 := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le, mul_pow]
  simp only [e]
  rw [← Finset.mul_sum]
  have hLh : ((2 * N + 1 : ℕ) : ℝ) * alh38 N = 1 := by
    rw [alh38_eq_inv, mul_inv_cancel₀ (by positivity)]
  linear_combination (-(alh38 N) * ∑ j, ‖v j‖ ^ 2) * hLh

theorem al041_term (N m : ℕ) (k : ℤ) :
    |alomega38 N k| ^ (2 * m)
      = (2 * Real.sin (Real.pi * (k : ℝ) / ((2 * N + 1 : ℕ) : ℝ))) ^ (2 * m) / (alh38 N) ^ (2 * m) := by
  have hpos := alh38_pos N
  have h1 : |alomega38 N k| * alh38 N = |alomega38 N k * alh38 N| := by
    rw [abs_mul, abs_of_pos hpos]
  have hk : alomega38 N k * alh38 N = 2 * Real.sin (Real.pi * (k : ℝ) * alh38 N) := by
    unfold alomega38
    exact div_mul_cancel₀ _ hpos.ne'
  have hang : Real.pi * (k : ℝ) * alh38 N = Real.pi * (k : ℝ) / ((2 * N + 1 : ℕ) : ℝ) := by
    rw [alh38_eq_inv]; ring
  rw [eq_div_iff (pow_ne_zero _ hpos.ne'), ← mul_pow, h1, hk, (even_two_mul m).pow_abs, hang]

theorem al041_two (N m : ℕ) (v : ZMod (2 * N + 1) → ℂ) :
    alh38 N * ∑ j, ‖(alDelta38^[m] v) j / (alh38 N : ℂ) ^ m‖ ^ 2
      = ∑ k ∈ Finset.Icc (-(N : ℤ)) N, |alomega38 N k| ^ (2 * m) * ‖alDFT38 N v k‖ ^ 2 := by
  have hpos := alh38_pos N
  have hC : ((alh38 N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hA := alDelta38_iterate_smul ((alh38 N : ℝ) : ℂ) m v
  have hT : ∀ j, ‖(alDelta38^[m] (fun j => ((alh38 N : ℝ) : ℂ) * v j)) j‖ ^ 2
      = (alh38 N) ^ 2 * ‖(alDelta38^[m] v) j‖ ^ 2 := by
    intro j
    rw [hA]
    dsimp only
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le, mul_pow]
  have hsq : ∀ j, ‖(alDelta38^[m] v) j / (alh38 N : ℂ) ^ m‖ ^ 2
      = ‖(alDelta38^[m] (fun j => ((alh38 N : ℝ) : ℂ) * v j)) j‖ ^ 2
          / (((alh38 N) ^ m) ^ 2 * (alh38 N) ^ 2) := by
    intro j
    rw [hT j, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    field_simp
  have hsum : ∑ j, ‖(alDelta38^[m] v) j / (alh38 N : ℂ) ^ m‖ ^ 2
      = (∑ j, ‖(alDelta38^[m] (fun j => ((alh38 N : ℝ) : ℂ) * v j)) j‖ ^ 2)
          / (((alh38 N) ^ m) ^ 2 * (alh38 N) ^ 2) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => hsq j
  have hI : ∑ k ∈ Finset.Icc (-(N : ℤ)) N, |alomega38 N k| ^ (2 * m) * ‖alDFT38 N v k‖ ^ 2
      = ∑ ν : ZMod (2 * N + 1), |alomega38 N ν.valMinAbs| ^ (2 * m) * ‖alDFT38 N v ν.valMinAbs‖ ^ 2 :=
    (sum_valMinAbs_eq_Icc38 N (fun ν => |alomega38 N ν| ^ (2 * m) * ‖alDFT38 N v ν‖ ^ 2)).symm
  rw [hsum, alDelta_parseval38 m (fun j => ((alh38 N : ℝ) : ℂ) * v j), hI]
  simp only [al041_dft]
  have hR : ∑ ν : ZMod (2 * N + 1),
      |alomega38 N ν.valMinAbs| ^ (2 * m) * ‖ZMod.dft (fun j => ((alh38 N : ℝ) : ℂ) * v j) ν‖ ^ 2
      = (∑ ν : ZMod (2 * N + 1),
          (2 * Real.sin (Real.pi * ((ν.valMinAbs : ℤ) : ℝ) / ((2 * N + 1 : ℕ) : ℝ))) ^ (2 * m)
            * ‖ZMod.dft (fun j => ((alh38 N : ℝ) : ℂ) * v j) ν‖ ^ 2) / (alh38 N) ^ (2 * m) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun ν _ => by rw [al041_term N m ν.valMinAbs]; ring
  rw [hR]
  have hLinv : ((2 * N + 1 : ℕ) : ℝ)⁻¹ = alh38 N := (alh38_eq_inv N).symm
  rw [hLinv]
  field_simp
  ring

theorem al041 (N m : ℕ) (v : ZMod (2 * N + 1) → ℂ) :
    alh38 N * ∑ j, ‖v j‖ ^ 2 =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ‖alDFT38 N v k‖ ^ 2 ∧
    alh38 N * ∑ j,
        ‖(alDelta38^[m] v) j / (alh38 N : ℂ) ^ m‖ ^ 2 =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        |alomega38 N k| ^ (2 * m) * ‖alDFT38 N v k‖ ^ 2 :=
  ⟨al041_one N v, al041_two N m v⟩

end NlsGge.ThirdConsultation.AL

