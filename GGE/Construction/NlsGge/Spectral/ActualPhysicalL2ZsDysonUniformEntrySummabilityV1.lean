import NlsGge.Spectral.ActualPhysicalL2ZsDysonFactorialBoundV1
import NlsGge.Spectral.ActualComplexZsDysonProductHasSumV2
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

theorem actualPhysicalL2ZsCumulativeMajorant_le_endpoint
    (u : PhysicalL2) (z : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    actualPhysicalL2ZsCumulativeMajorant u z t ≤
      actualPhysicalL2ZsCumulativeMajorant u z 2 := by
  exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    (Filter.Eventually.of_forall (actualPhysicalL2ZsMajorant_nonneg u z))
    (actualPhysicalL2ZsMajorant_intervalIntegrable u z)

/-- A single summable scalar bound controls all entries on the true doubled
interval, for each actual physical L² field and complex spectral parameter. -/
theorem actualPhysicalL2ZsDysonTerm_entry_uniform_bound
    (u : PhysicalL2) (z : ℂ) (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 2) (i j : Fin 2) :
    ‖actualComplexZsDysonTerm
      (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      z n t i j‖ ≤
      (2 * actualPhysicalL2ZsCumulativeMajorant u z 2) ^ n / (n.factorial : ℝ) := by
  have h := actualPhysicalL2ZsDysonTerm_entry_factorial_bound u z n t ht i j
  have hpow := pow_le_pow_left₀
    (actualPhysicalL2ZsCumulativeMajorant_nonneg u z t ht.1)
    (actualPhysicalL2ZsCumulativeMajorant_le_endpoint u z t ht) n
  calc
    _ ≤ (2 ^ n / (n.factorial : ℝ)) *
      actualPhysicalL2ZsCumulativeMajorant u z t ^ n := h
    _ ≤ (2 ^ n / (n.factorial : ℝ)) *
      actualPhysicalL2ZsCumulativeMajorant u z 2 ^ n :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem summable_actualPhysicalL2ZsDysonTerm_entry
    (u : PhysicalL2) (z : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2)
    (i j : Fin 2) :
    Summable (fun n : ℕ => actualComplexZsDysonTerm
      (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      z n t i j) := by
  exact Summable.of_norm_bounded
    (NormedSpace.expSeries_div_hasSum_exp
      (2 * actualPhysicalL2ZsCumulativeMajorant u z 2)).summable
    (fun n => actualPhysicalL2ZsDysonTerm_entry_uniform_bound u z n t ht i j)

/-- Pointwise multiplication by the actual rough coefficient preserves the
actual Dyson series; no boundedness of the field representative is assumed. -/
theorem hasSum_actualPhysicalL2ZsDysonProduct_entry
    (u : PhysicalL2) (z : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2)
    (i j : Fin 2) :
    HasSum
      (fun n : ℕ => (zsCoefficientComplex
        (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
        z t * actualComplexZsDysonTerm
        (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
        z n t) i j)
      ((zsCoefficientComplex
        (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
        z t * actualComplexZsDysonTsum
        (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
        z t) i j) := by
  let U : ℝ → ℂ := fun s =>
    (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle)
  have h0 := (summable_actualPhysicalL2ZsDysonTerm_entry u z t ht 0 j).hasSum
  have h1 := (summable_actualPhysicalL2ZsDysonTerm_entry u z t ht 1 j).hasSum
  have hsum := (h0.mul_left (zsCoefficientComplex U z t i 0)).add
    (h1.mul_left (zsCoefficientComplex U z t i 1))
  simpa only [actualComplexZsDysonTsum, Matrix.mul_apply, Fin.sum_univ_two] using hsum
end NlsGge.SpectralFoundations
end
