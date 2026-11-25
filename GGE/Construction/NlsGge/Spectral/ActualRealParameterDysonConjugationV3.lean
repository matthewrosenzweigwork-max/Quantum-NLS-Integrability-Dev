import NlsGge.Spectral.ActualPhysicalL2ZsDysonUniformEntrySummabilityV1
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Entrywise conjugation reverses BOTH channels for the actual ZS
coefficient at a real spectral parameter; this is not matrix adjoint. -/
theorem zsCoefficientComplex_real_entry_star
    (U : ℝ → ℂ) (r t : ℝ) (i j : Fin 2) :
    star (zsCoefficientComplex U (r : ℂ) t i j) =
      zsCoefficientComplex U (r : ℂ) t i.rev j.rev := by
  fin_cases i <;> fin_cases j <;>
    simp [zsCoefficientComplex, Fin.rev, star_mul, star_neg, Complex.star_def, mul_comm]

/-- The actual nested interval integrals inherit the entrywise symmetry.
The equality is algebraic for totalized integrals; the actual physical L²
realization separately supplies the already proved convergence bounds. -/
theorem actualComplexZsDysonTerm_real_entry_star
    (U : ℝ → ℂ) (r : ℝ) (n : ℕ) (t : ℝ) (i j : Fin 2) :
    star (actualComplexZsDysonTerm U (r : ℂ) n t i j) =
      actualComplexZsDysonTerm U (r : ℂ) n t i.rev j.rev := by
  induction n generalizing t i j with
  | zero =>
    fin_cases i <;> fin_cases j <;>
      simp [actualComplexZsDysonTerm, Matrix.one_apply, Fin.rev]
  | succ n ih =>
    change star (∫ s in (0 : ℝ)..t,
      (zsCoefficientComplex U (r : ℂ) s * actualComplexZsDysonTerm U (r : ℂ) n s) i j) =
      ∫ s in (0 : ℝ)..t,
        (zsCoefficientComplex U (r : ℂ) s * actualComplexZsDysonTerm U (r : ℂ) n s) i.rev j.rev
    have hconj : star (∫ s in (0 : ℝ)..t,
        (zsCoefficientComplex U (r : ℂ) s * actualComplexZsDysonTerm U (r : ℂ) n s) i j) =
        ∫ s in (0 : ℝ)..t,
          star ((zsCoefficientComplex U (r : ℂ) s * actualComplexZsDysonTerm U (r : ℂ) n s) i j) := by
      simpa only [Complex.star_def] using
        (intervalIntegral.intervalIntegral_conj (f := fun s =>
          (zsCoefficientComplex U (r : ℂ) s * actualComplexZsDysonTerm U (r : ℂ) n s) i j)).symm
    rw [hconj]
    apply intervalIntegral.integral_congr
    intro s hs
    simp only [Matrix.mul_apply, Fin.sum_univ_two, star_add, star_mul,
      zsCoefficientComplex_real_entry_star, ih]
    fin_cases i <;> fin_cases j <;> simp [Fin.rev] <;> ring

theorem actualComplexZsDysonTsum_real_entry_star
    (U : ℝ → ℂ) (r t : ℝ) (i j : Fin 2) :
    star (actualComplexZsDysonTsum U (r : ℂ) t i j) =
      actualComplexZsDysonTsum U (r : ℂ) t i.rev j.rev := by
  simp only [actualComplexZsDysonTsum, Complex.star_def, Complex.conj_tsum]
  apply tsum_congr
  intro n
  simpa only [Complex.star_def] using
    actualComplexZsDysonTerm_real_entry_star U r n t i j

/-- The genuine full rough fundamental trace is real at real spectral
parameters. This does not identify spectral roots, gaps or actions. -/
theorem actualPhysicalL2ZsFullTrace_real
    (u : PhysicalL2) (r t : ℝ) :
    star (Matrix.trace (actualComplexZsDysonTsum
      (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      (r : ℂ) t)) =
    Matrix.trace (actualComplexZsDysonTsum
      (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      (r : ℂ) t) := by
  simp only [Matrix.trace_fin_two, star_add, actualComplexZsDysonTsum_real_entry_star]
  simp [Fin.rev, add_comm]

end NlsGge.SpectralFoundations
end
