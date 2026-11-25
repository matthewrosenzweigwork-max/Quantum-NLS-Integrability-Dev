import NlsGge.Spectral.ActualComplexMatrixTwoByTwoEntrySupProductBoundV2
import NlsGge.Spectral.IntervalIntegralTwoProductWeightedEntryBoundV5
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

theorem norm_intervalIntegral_matrix_product_weighted_entry_le
    (A B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) (n : ℕ)
    (t M D : ℝ) (ht : 0 ≤ t) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hA : ∀ s ∈ Set.Icc (0 : ℝ) t,
      actualComplexMatrixEntrySup (A s) ≤ M)
    (hB : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ k l : Fin 2,
      ‖B s k l‖ ≤ D * s ^ n) :
    ‖∫ s in (0 : ℝ)..t, (A s * B s) i j‖ ≤
      2 * M * D * t ^ (n + 1) / (n + 1 : ℝ) := by
  have hf₀ (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) t) : ‖A s i 0‖ ≤ M :=
    le_trans (norm_entry_le_actualComplexMatrixEntrySup (A s) i 0) (hA s hs)
  have hf₁ (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) t) : ‖A s i 1‖ ≤ M :=
    le_trans (norm_entry_le_actualComplexMatrixEntrySup (A s) i 1) (hA s hs)
  have hg₀ (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) t) : ‖B s 0 j‖ ≤ D * s ^ n := hB s hs 0 j
  have hg₁ (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) t) : ‖B s 1 j‖ ≤ D * s ^ n := hB s hs 1 j
  simpa only [Matrix.mul_apply, Fin.sum_univ_two] using
    (norm_intervalIntegral_two_products_weighted_le
      (fun s => A s i 0) (fun s => A s i 1)
      (fun s => B s 0 j) (fun s => B s 1 j)
      n t M D ht hM hD hf₀ hf₁ hg₀ hg₁)

end NlsGge.SpectralFoundations
