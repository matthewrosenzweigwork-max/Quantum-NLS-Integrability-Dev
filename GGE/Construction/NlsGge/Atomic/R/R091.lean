                                                                                                                                                                                                                                                                                 
import Mathlib
import NlsGge.Composition.FourierDecay

                                                                                                                          
                                                                                                     
                                                                                                                  
                                                                                                                
                                                                                                                
                                                                    

set_option autoImplicit false

open AddCircle MeasureTheory

namespace NlsGge.Atomic.R091

theorem fourierCoeff_norm_le_of_iteratedDeriv_infty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {K s : ℝ} (U : AddCircle (1 : ℝ) → E)
    (hU : ∀ m : ℕ, ContDiff ℝ m (fun x : ℝ => U x))
    (hD : ∀ (m : ℕ) (x : ℝ), ‖iteratedDeriv m (fun x : ℝ => U x) x‖ ≤ K * m.factorial / s ^ m)
    (n : ℤ) :
    ‖fourierCoeff U n‖ ≤ 2 * K * Real.exp (-(Real.pi * s) * |(n : ℝ)|) := by
  by_cases hs : 0 < s
  · exact NlsGge.Composition.fourierCoeff_norm_le_of_iteratedDeriv_infty U hU hs hD n
  · push_neg at hs
    have hK0 : 0 ≤ K := by
      have h := hD 0 0
      rw [iteratedDeriv_zero, Nat.factorial_zero, pow_zero, Nat.cast_one, mul_one, div_one] at h
      exact le_trans (norm_nonneg _) h
    have hbd : ∀ x : AddCircle (1 : ℝ), ‖U x‖ ≤ K := by
      intro x
      obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective x
      have h := hD 0 r
      rw [iteratedDeriv_zero, Nat.factorial_zero, pow_zero, Nat.cast_one, mul_one, div_one] at h
      exact h
    have hnorm : ‖fourierCoeff U n‖ ≤ K := by
      unfold fourierCoeff
      have h := norm_integral_le_of_norm_le_const (μ := haarAddCircle)
        (f := fun t : AddCircle (1 : ℝ) => fourier (-n) t • U t) (C := K)
        (Filter.Eventually.of_forall (fun t => by
          have hf : ‖fourier (-n) t‖ = 1 := by
            rw [fourier_apply]
            exact Circle.norm_coe _
          rw [norm_smul, hf, one_mul]
          exact hbd t))
      simpa using h
    have hpi : 0 ≤ -(Real.pi * s) := by nlinarith [Real.pi_pos]
    have hexp : 1 ≤ Real.exp (-(Real.pi * s) * |(n : ℝ)|) :=
      Real.one_le_exp (mul_nonneg hpi (abs_nonneg _))
    calc ‖fourierCoeff U n‖ ≤ K := hnorm
      _ ≤ 2 * K * Real.exp (-(Real.pi * s) * |(n : ℝ)|) := by nlinarith [hK0, hexp]

end NlsGge.Atomic.R091

