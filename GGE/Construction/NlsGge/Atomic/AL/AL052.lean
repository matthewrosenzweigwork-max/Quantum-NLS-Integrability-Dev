import Mathlib


namespace NlsGge.Atomic.AL052

                                                                                                                
                                                                                                                    

theorem AL052_series :
  ∀ r : ℝ, 0 ≤ r → r < 1 →
    HasSum (fun m : ℕ => r ^ (m + 2) / ((m : ℝ) + 2)) (-Real.log (1 - r) - r) ∧
    0 ≤ -Real.log (1 - r) - r ∧
    HasSum (fun m : ℕ => r ^ (m + 3) / ((m : ℝ) + 3)) (-Real.log (1 - r) - r - r ^ 2 / 2) ∧
    0 ≤ -Real.log (1 - r) - r - r ^ 2 / 2 := by
  intro r h0 h1
  have habs : |r| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have hL := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have hA : HasSum (fun m : ℕ => r ^ (m + 2) / ((m : ℝ) + 2)) (-Real.log (1 - r) - r) := by
    have h := (hasSum_nat_add_iff' 1).mpr hL
    convert h using 1
    · funext m
      push_cast
      ring_nf
    · simp
  have hAnn : 0 ≤ -Real.log (1 - r) - r :=
    hA.nonneg (fun m => by positivity)
  have hB : HasSum (fun m : ℕ => r ^ (m + 3) / ((m : ℝ) + 3)) (-Real.log (1 - r) - r - r ^ 2 / 2) := by
    have h := (hasSum_nat_add_iff' 1).mpr hA
    convert h using 1
    · funext m
      push_cast
      ring_nf
    · simp
  have hBnn : 0 ≤ -Real.log (1 - r) - r - r ^ 2 / 2 :=
    hB.nonneg (fun m => by positivity)
  exact ⟨hA, hAnn, hB, hBnn⟩
end NlsGge.Atomic.AL052
