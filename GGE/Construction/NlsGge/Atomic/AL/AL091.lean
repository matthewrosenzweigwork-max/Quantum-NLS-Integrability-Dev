import Mathlib

namespace NlsGge.Atomic.AL091


                                                                                                                                            
set_option autoImplicit false


theorem AL091_main : (((∫ x in (0 : ℝ)..(1 / 2), (Real.sqrt (2 * Real.sin (Real.pi * x)) - Real.sqrt (2 * Real.pi * x))) < 0 ∧
    ContinuousOn (fun x : ℝ => Real.sqrt (2 * Real.sin (Real.pi * x)) - Real.sqrt (2 * Real.pi * x))
      (Set.Icc 0 (1 / 2)) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
      Real.sqrt (2 * Real.sin (Real.pi * x)) - Real.sqrt (2 * Real.pi * x) ≤ 0) ∧
    (∀ x ∈ Set.Ioc (0 : ℝ) (1 / 2),
      Real.sqrt (2 * Real.sin (Real.pi * x)) - Real.sqrt (2 * Real.pi * x) < 0)) : Prop) := by
  have hcont : Continuous (fun x : ℝ => Real.sqrt (2 * Real.sin (Real.pi * x)) - Real.sqrt (2 * Real.pi * x)) := by
    fun_prop
  have hlt : ∀ x ∈ Set.Ioc (0 : ℝ) (1 / 2),
      Real.sqrt (2 * Real.sin (Real.pi * x)) - Real.sqrt (2 * Real.pi * x) < 0 := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hpix : 0 < Real.pi * x := mul_pos Real.pi_pos hx0
    have hs0 : 0 ≤ Real.sin (Real.pi * x) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hpix.le (by nlinarith [Real.pi_pos, hx.2])
    have hlt' : 2 * Real.sin (Real.pi * x) < 2 * Real.pi * x := by
      have := Real.sin_lt hpix
      linarith
    have := Real.sqrt_lt_sqrt (by linarith) hlt'
    linarith
  refine ⟨?_, hcont.continuousOn, ?_, hlt⟩
  · have hpos : 0 < ∫ x in (0 : ℝ)..(1 / 2),
        (Real.sqrt (2 * Real.pi * x) - Real.sqrt (2 * Real.sin (Real.pi * x))) := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx => ?_) (by norm_num)
      · exact (by fun_prop : Continuous (fun x : ℝ => Real.sqrt (2 * Real.pi * x) - Real.sqrt (2 * Real.sin (Real.pi * x)))).intervalIntegrable _ _
      · have := hlt x ⟨hx.1, hx.2.le⟩
        linarith
    have hneg : (∫ x in (0 : ℝ)..(1 / 2),
        (Real.sqrt (2 * Real.pi * x) - Real.sqrt (2 * Real.sin (Real.pi * x)))) =
        -∫ x in (0 : ℝ)..(1 / 2), (Real.sqrt (2 * Real.sin (Real.pi * x)) - Real.sqrt (2 * Real.pi * x)) := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr (fun x _ => by simp)
    linarith
  · intro x hx
    rcases hx.1.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · exact (hlt x ⟨h0, hx.2⟩).le


end NlsGge.Atomic.AL091
