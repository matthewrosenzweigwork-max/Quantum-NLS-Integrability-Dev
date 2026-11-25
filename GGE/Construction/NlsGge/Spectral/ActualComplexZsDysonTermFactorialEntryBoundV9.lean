import NlsGge.Spectral.ActualComplexZsFiniteDysonIteratesContinuousV9
import NlsGge.Spectral.IntervalIntegralMatrixProductWeightedEntryBoundV6
import NlsGge.Spectral.ActualComplexZsCoefficientEntrySupBoundV4
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

theorem actualComplexZsDysonTerm_entry_factorial_bound
    (u : ℝ → ℂ) (z : ℂ) (R C : ℝ)
    (hz : ‖z‖ ≤ R) (hR : 0 ≤ R)
    (hU : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖u s‖ ≤ C) (hC : 0 ≤ C) :
    ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 2 → ∀ i j : Fin 2,
      ‖actualComplexZsDysonTerm u z n t i j‖ ≤
        ((2 * (R + C)) ^ n / (n.factorial : ℝ)) * t ^ n := by
  have hM : 0 ≤ R + C := add_nonneg hR hC
  intro n
  induction n with
  | zero =>
      intro t ht i j
      by_cases hij : i = j <;>
        simp [actualComplexZsDysonTerm, Matrix.one_apply, hij]
  | succ n ih =>
      intro t ht i j
      have hA : ∀ s ∈ Set.Icc (0 : ℝ) t,
          actualComplexMatrixEntrySup (zsCoefficientComplex u z s) ≤ R + C := by
        intro s hs
        have hs2 : s ∈ Set.Icc (0 : ℝ) 2 := ⟨hs.1, le_trans hs.2 ht.2⟩
        exact actualComplexZsCoefficient_entrySup_bound u z s R C hz (hU s hs2)
      have hB : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ k l : Fin 2,
          ‖actualComplexZsDysonTerm u z n s k l‖ ≤
            (((2 * (R + C)) ^ n / (n.factorial : ℝ)) * s ^ n) := by
        intro s hs k l
        have hs2 : s ∈ Set.Icc (0 : ℝ) 2 := ⟨hs.1, le_trans hs.2 ht.2⟩
        exact ih s hs2 k l
      have hstep := norm_intervalIntegral_matrix_product_weighted_entry_le
        (fun s => zsCoefficientComplex u z s)
        (fun s => actualComplexZsDysonTerm u z n s)
        i j n t (R + C) (((2 * (R + C)) ^ n) / (n.factorial : ℝ)) ht.1 hM
        (by positivity) hA hB
      have hfactorial : ((n + 1).factorial : ℝ) =
          (n + 1 : ℝ) * (n.factorial : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      rw [actualComplexZsDysonTerm]
      calc
        ‖∫ s in (0 : ℝ)..t,
            (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j‖ ≤
            2 * (R + C) * (((2 * (R + C)) ^ n) / (n.factorial : ℝ)) *
              t ^ (n + 1) / (n + 1 : ℝ) := hstep
        _ = ((2 * (R + C)) ^ (n + 1) / ((n + 1).factorial : ℝ)) *
              t ^ (n + 1) := by
          rw [hfactorial]
          have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
          have hfac : (n.factorial : ℝ) ≠ 0 := by
            exact_mod_cast Nat.factorial_ne_zero n
          field_simp [hn1, hfac]
          <;> ring

end NlsGge.SpectralFoundations
