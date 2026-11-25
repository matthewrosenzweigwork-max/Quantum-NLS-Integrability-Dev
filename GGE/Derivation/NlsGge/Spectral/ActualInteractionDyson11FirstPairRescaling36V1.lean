import NlsGge.Spectral.ActualInteractionDyson11PhaseRescaling35V1
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations

/-- Exact `k = 0` specialization of the actual rescaled 11 Dyson recurrence.
The zero-order diagonal is one, so the inner factor is precisely
`U(r) * phase(2*x)(r) * exp(-2*Y*r)`. This is only a finite-order identity;
it makes no Fourier-tail or all-orders assertion. -/
theorem actualInteractionDyson11_firstPairRescaling36V1
    (U : ℝ → ℂ) (x Y t : ℝ) :
    (Real.exp (-2*Y*t) : ℂ) *
      genericRoughMatrixDysonTerm32
        (actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ)))
        2 t 1 1 =
      ∫ s in (0 : ℝ)..t,
        (Real.exp (-2*Y*(t-s)) : ℂ) * complexRealOscillatoryPhase35 (-2*x) s *
          star (U s) *
          (∫ r in (0 : ℝ)..s,
            U r * (complexRealOscillatoryPhase35 (2*x) r *
              (Real.exp (-2*Y*r) : ℂ))) := by
  have hzero (r : ℝ) :
      genericRoughMatrixDysonTerm32
        (actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ)))
        0 r 1 1 = 1 := by
    simp [genericRoughMatrixDysonTerm32, Matrix.one_apply]
  have h := actualInteractionDyson11_phaseRescaling35 U x Y 0 t
  simpa only [Nat.mul_zero, Nat.zero_add, hzero, mul_one] using h

end NlsGge.SpectralFoundations
end
