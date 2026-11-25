import NlsGge.Spectral.GenericRoughDysonAECongruence36V4
import NlsGge.Spectral.ActualPhysicalInteractionStripMajorant36V3
import NlsGge.Spectral.ActualPhysicalInteractionDysonIdentification32V2
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
open CumulativePowerV3
/-- The actual finite-term representative identity and a realized factorial
majorant make the interaction Dyson sum continuous along the real coupling
path. This does not assume or select any Floquet root or logarithm. -/
theorem actualPhysicalInteractionDyson_coupling_continuousOn36V2
    (u : PhysicalL2) (z : ℂ) (Y₀ : ℝ)
    (hY₀ : 0 ≤ Y₀) (hY : 0 ≤ z.im) (hY' : z.im ≤ Y₀)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ContinuousOn (fun τ : ℝ => genericRoughMatrixDysonTsum32
      (actualZsInteractionCoefficient32
        (fun s => naturalPhysicalCoverL2 ((τ : ℂ) • u) (s : SpectralCircle)) z)
      t i j) (Set.Icc (0 : ℝ) 1) := by
  let B := actualZsInteractionCoefficient32
    (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) z
  let f : ℕ → ℝ → ℂ := fun n τ => (τ : ℂ)^n * genericRoughMatrixDysonTerm32 B n t i j
  let q := actualPhysicalInteractionStripMajorant36V3 u Y₀
  let b : ℕ → ℝ := fun n => (2 * actualCumulativeRealIntegral q 1)^n / (n.factorial : ℝ)
  have hf (n : ℕ) : ContinuousOn (f n) (Set.Icc (0 : ℝ) 1) := by
    exact ((Complex.continuous_ofReal.pow n).mul continuous_const).continuousOn
  have hb : Summable b := (NormedSpace.expSeries_div_hasSum_exp
    (2 * actualCumulativeRealIntegral q 1)).summable
  have hbound (n : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : ‖f n τ‖ ≤ b n := by
    have hnorm : ‖(τ : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ.1] using hτ.2
    have hp : ‖(τ : ℂ)^n‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hnorm
    have hterm := actualPhysicalInteractionDysonTerm_factorial_boundedHeight36V3
      u z Y₀ hY₀ hY hY' n t ht i j
    dsimp [f]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans hterm
  have hseries := continuousOn_tsum hf hb hbound
  have heq (τ : ℝ) : genericRoughMatrixDysonTsum32
      (actualZsInteractionCoefficient32
        (fun s => naturalPhysicalCoverL2 ((τ : ℂ) • u) (s : SpectralCircle)) z)
      t i j = ∑' n : ℕ, f n τ := by
    unfold genericRoughMatrixDysonTsum32
    apply tsum_congr
    intro n
    have h := actualPhysicalInteractionDysonTerm_realCoupling36V4 u τ z n t ht
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) h
    simpa only [B, f, Matrix.smul_apply, smul_eq_mul] using he
  exact hseries.congr (fun τ hτ => heq τ)
end NlsGge.SpectralFoundations
end
