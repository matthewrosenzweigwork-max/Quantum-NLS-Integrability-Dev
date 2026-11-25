import NlsGge.Spectral.ActualInteractionPairKernel32V2
import NlsGge.Spectral.ComplexRealOscillatoryPhase35V1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations

/-- Exact concrete 00 recurrence at arbitrary real frequency and positive-height parameter. Unlike the 11
recurrence, this channel already has height decay without rescaling. -/
theorem actualInteractionDyson00_phaseRecurrence35
    (U : ℝ → ℂ) (x Y : ℝ) (k : ℕ) (t : ℝ) :
    genericRoughMatrixDysonTerm32
      (actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ))) (2*k+2) t 0 0 =
      ∫ s in (0 : ℝ)..t, U s*complexRealOscillatoryPhase35 (2*x) s*
        (∫ r in (0 : ℝ)..s, (Real.exp (-2*Y*(s-r)) : ℂ)*star (U r)*(complexRealOscillatoryPhase35 (-2*x) r*
          genericRoughMatrixDysonTerm32
            (actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ))) (2*k) r 0 0)) := by
  rw [(actualInteractionDyson_pair_recurrence32 U ((x : ℂ)+Complex.I*(Y : ℂ)) k t).1]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  have h := (actualInteractionPairKernel32 U ((x : ℂ)+Complex.I*(Y : ℂ)) s r).1
  rw [complexUpperHalfPlanePairExponential_phaseFactor35] at h
  calc
    _ = (actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ)) s 0 1*
          actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ)) r 1 0)*
        genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ))) (2*k) r 0 0 := by ring
    _ = (U s*star (U r)*((Real.exp (-2*Y*(s-r)) : ℂ)*
          complexRealOscillatoryPhase35 (2*x) s*complexRealOscillatoryPhase35 (-2*x) r))*
        genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ))) (2*k) r 0 0 := by rw [h]
    _ = _ := by ring

end NlsGge.SpectralFoundations
end
