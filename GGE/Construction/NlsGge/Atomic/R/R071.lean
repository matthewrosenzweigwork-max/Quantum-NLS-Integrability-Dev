import Mathlib


namespace NlsGge.Atomic.R071

                                                                                                                                                                                                              
                                                

theorem R071_poisson_moments :
  ∀ t : ℝ, 0 < t →
    HasSum (fun j : ℕ => Real.exp (-t) * t ^ j / (j.factorial : ℝ)) 1 ∧
    HasSum (fun j : ℕ => (j : ℝ) * (Real.exp (-t) * t ^ j / (j.factorial : ℝ))) t ∧
    HasSum (fun j : ℕ => ((j : ℝ) - t) ^ 2 * (Real.exp (-t) * t ^ j / (j.factorial : ℝ))) t := by
  intro t _
  have h0 : HasSum (fun j : ℕ => t ^ j / (j.factorial : ℝ)) (Real.exp t) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp t
  have hE : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]; simp
  -- j * a_j = t * a_{j-1}
  have hj1 : HasSum (fun j : ℕ => (j : ℝ) * (t ^ j / (j.factorial : ℝ))) (t * Real.exp t) := by
    rw [← hasSum_nat_add_iff' 1]
    convert h0.mul_left t using 1
    · funext n
      push_cast
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · simp
  -- j (j-1) a_j = t^2 a_{j-2}
  have hj2 : HasSum (fun j : ℕ => (j : ℝ) * ((j : ℝ) - 1) * (t ^ j / (j.factorial : ℝ)))
      (t ^ 2 * Real.exp t) := by
    rw [← hasSum_nat_add_iff' 2]
    convert h0.mul_left (t ^ 2) using 1
    · funext n
      push_cast
      rw [Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · simp [Finset.sum_range_succ]
  have hmass : HasSum (fun j : ℕ => Real.exp (-t) * t ^ j / (j.factorial : ℝ)) 1 := by
    have := h0.mul_left (Real.exp (-t))
    rw [hE] at this
    convert this using 1
    funext j
    ring
  have hmean : HasSum (fun j : ℕ => (j : ℝ) * (Real.exp (-t) * t ^ j / (j.factorial : ℝ))) t := by
    have := hj1.mul_left (Real.exp (-t))
    convert this using 1
    · funext j; ring
    · linear_combination (-t) * hE
  have hvar : HasSum (fun j : ℕ => ((j : ℝ) - t) ^ 2 * (Real.exp (-t) * t ^ j / (j.factorial : ℝ))) t := by
    have hcomb := ((hj2.add hj1).sub ((hj1.mul_left (2 * t)))).add (h0.mul_left (t ^ 2))
    have := hcomb.mul_left (Real.exp (-t))
    convert this using 1
    · funext j; ring
    · linear_combination (-t) * hE
  exact ⟨hmass, hmean, hvar⟩
end NlsGge.Atomic.R071
