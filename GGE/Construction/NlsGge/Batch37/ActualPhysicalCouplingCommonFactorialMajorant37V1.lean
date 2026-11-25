import NlsGge.Spectral.ActualPhysicalInteractionCouplingContinuity36V2
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
open CumulativePowerV3
/-- The same actual bounded-height factorial majorant controls every actual
raw-cover real coupling tau in[0,1]. This exposes the common bound previously
realized locally in the actual coupling-continuity proof. -/
theorem actualPhysicalInteractionDysonTerm_coupling_commonFactorialMajorant37V1
    (u : PhysicalL2) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (z : ℂ) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (hY : 0 ≤ z.im) (hY' : z.im ≤ Y₀)
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖genericRoughMatrixDysonTerm32
      (actualZsInteractionCoefficient32
        (fun s => naturalPhysicalCoverL2 ((τ : ℂ) • u) (s : SpectralCircle)) z)
      n t i j‖ ≤
      (2 * actualCumulativeRealIntegral
        (actualPhysicalInteractionStripMajorant36V3 u Y₀) 1) ^ n /
        (n.factorial : ℝ) := by
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j)
    (actualPhysicalInteractionDysonTerm_realCoupling36V4 u τ z n t ht)
  simp only [Matrix.smul_apply, smul_eq_mul] at he
  have hnorm : ‖(τ : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ.1] using hτ.2
  have hp : ‖(τ : ℂ)^n‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hnorm
  rw [he, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans
    (actualPhysicalInteractionDysonTerm_factorial_boundedHeight36V3
      u z Y₀ hY₀ hY hY' n t ht i j)
end NlsGge.SpectralFoundations
end
