import NlsGge.Spectral.ActualInteractionPairKernel32V2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
/-- Exact first actual 00 pair, before estimates or any choice of height.
The identity uses the concrete interaction coefficient, not a formal kernel
or a pointwise choice of an Lp representative. -/
theorem actualInteractionDyson00_firstPairIdentity36V1
    (U : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    genericRoughMatrixDysonTerm32 (actualZsInteractionCoefficient32 U z) 2 t 0 0 =
      ∫ s in (0 : ℝ)..t, U s *
        (∫ r in (0 : ℝ)..s,
          Complex.exp (2 * Complex.I * z * ((s-r : ℝ) : ℂ)) * star (U r)) := by
  have hzero (r : ℝ) :
      genericRoughMatrixDysonTerm32 (actualZsInteractionCoefficient32 U z) 0 r 0 0 = 1 := by
    simp [genericRoughMatrixDysonTerm32, Matrix.one_apply]
  have hrec := (actualInteractionDyson_pair_recurrence32 U z 0 t).1
  simp only [Nat.mul_zero, Nat.zero_add, hzero, mul_one] at hrec
  rw [hrec]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [(actualInteractionPairKernel32 U z s r).1]
  ring
end NlsGge.SpectralFoundations
end
