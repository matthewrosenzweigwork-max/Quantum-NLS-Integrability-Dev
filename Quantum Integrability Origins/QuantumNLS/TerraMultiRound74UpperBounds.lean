import QuantumNLS.TerraMultiRound74UniformSmall

/-! Upper-interval correction bounds, importing REG-014 for large Y. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound74UpperBounds
open QuantumNLS.TranslatedCorrelation QuantumNLS.Reg014Moments
open QuantumNLS.TerraMultiRound74UniformSmall

variable {L : ℝ} [Fact (0 < L)]

/-- The physical correction has a common quadratic bound near zero and a
common constant bound away from zero on any bounded H¹ set. -/
theorem correction_bounds (κ : ℝ) (hκ : 0 < κ) (B : Set (Hk L 1))
    (hB : Bornology.IsBounded B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ B, ∀ Y : ℝ, 0 < Y →
      |Dfun κ hκ 2 u.val Y| ≤ C * (if Y ≤ 1 then Y ^ 2 else 1) := by
  obtain ⟨A, hA, hs⟩ := physical_small_uniform κ hκ B hB
  obtain ⟨D, Y₀, hD, hY₀, hl⟩ := (QuantumNLS.Reg014Main.REG014 L κ hκ 2 (by omega)).2.2 B hB
  let C := max A (max D (A * (max Y₀ 1) ^ 2))
  have hC0 : 0 ≤ C := hA.trans (le_max_left _ _)
  refine ⟨C, hC0, ?_⟩
  intro u hu Y hY
  by_cases hy1 : Y ≤ 1
  · simp only [if_pos hy1]
    exact (hs u hu Y hY).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg Y))
  · simp only [if_neg hy1, mul_one]
    by_cases hy0 : Y₀ ≤ Y
    · have h := hl u hu Y hy0
      change |Dfun κ hκ 2 u.val Y| ≤ D at h
      exact h.trans ((le_max_left _ _).trans (le_max_right _ _))
    · have hy : Y ≤ max Y₀ 1 := (le_of_not_ge hy0).trans (le_max_left _ _)
      have hsq : Y ^ 2 ≤ (max Y₀ 1) ^ 2 := pow_le_pow_left₀ hY.le hy 2
      exact (hs u hu Y hY).trans ((mul_le_mul_of_nonneg_left hsq hA).trans
        ((le_max_right _ _).trans (le_max_right _ _)))

#print axioms correction_bounds
end QuantumNLS.TerraMultiRound74UpperBounds
