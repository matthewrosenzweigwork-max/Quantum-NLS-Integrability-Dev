import NlsGge.Spectral.ActualInteractionPairKernel32V2
import NlsGge.Spectral.ComplexOppositeOscillatoryPairPhase35V1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations

/-- Exact opposite-channel pair rescaling at arbitrary real frequency and height. The complex
potential product is preserved; no reality or pointwise regularity of U is
assumed. This is an algebra identity, not a tail estimate. -/
theorem actualInteractionPair11_phaseRescaling35
    (U : ℝ → ℂ) (x Y t s r : ℝ) :
    (Real.exp (-2*Y*t) : ℂ) *
      (actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ)) s 1 0 *
        actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ)) r 0 1) =
    (Real.exp (-2*Y*(t-s)) : ℂ) * complexRealOscillatoryPhase35 (-2*x) s *
      star (U s) * U r * complexRealOscillatoryPhase35 (2*x) r *
      (Real.exp (-2*Y*r) : ℂ) := by
  rw [(actualInteractionPairKernel32 U ((x : ℂ)+Complex.I*(Y : ℂ)) s r).2]
  rw [complexUpperHalfPlaneOppositePairExponential_phaseFactor35]
  have hexp : (Real.exp (-2*Y*t) : ℂ) * (Real.exp (2*Y*(s-r)) : ℂ) =
      (Real.exp (-2*Y*(t-s)) : ℂ) * (Real.exp (-2*Y*r) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  calc
    _ = (star (U s) * U r) *
        (complexRealOscillatoryPhase35 (-2*x) s*complexRealOscillatoryPhase35 (2*x) r)*
        ((Real.exp (-2*Y*t) : ℂ) * (Real.exp (2*Y*(s-r)) : ℂ)) := by ring
    _ = (star (U s) * U r) *
        (complexRealOscillatoryPhase35 (-2*x) s*complexRealOscillatoryPhase35 (2*x) r)*
        ((Real.exp (-2*Y*(t-s)) : ℂ) * (Real.exp (-2*Y*r) : ℂ)) := by rw [hexp]
    _ = _ := by ring

/-- Exact nested recurrence for the rescaled even 11 Dyson coefficient.
Only constants are moved through interval integrals; no Fubini or assumed
high-energy estimate is used. Actual rough-source regularity enters the
subsequent bounds, not this algebraic recurrence. -/
theorem actualInteractionDyson11_phaseRescaling35
    (U : ℝ → ℂ) (x Y : ℝ) (k : ℕ) (t : ℝ) :
    (Real.exp (-2*Y*t) : ℂ) *
      genericRoughMatrixDysonTerm32 (actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ)))
        (2*k+2) t 1 1 =
    (∫ s in (0 : ℝ)..t, (Real.exp (-2*Y*(t-s)) : ℂ) * complexRealOscillatoryPhase35 (-2*x) s * star (U s) *
      (∫ r in (0 : ℝ)..s, U r * (complexRealOscillatoryPhase35 (2*x) r*((Real.exp (-2*Y*r) : ℂ) *
        genericRoughMatrixDysonTerm32 (actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ)))
          (2*k) r 1 1)))) := by
  rw [(actualInteractionDyson_pair_recurrence32 U ((x : ℂ)+Complex.I*(Y : ℂ)) k t).2,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  let D : ℝ → ℂ := fun r => genericRoughMatrixDysonTerm32
    (actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ))) (2*k) r 1 1
  calc
    _ = ((Real.exp (-2*Y*t) : ℂ) *
        actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ)) s 1 0) *
      (∫ r in (0 : ℝ)..s,
        actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ)) r 0 1 * D r) := by ring
    _ = ∫ r in (0 : ℝ)..s,
        ((Real.exp (-2*Y*t) : ℂ) *
          actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ)) s 1 0) *
        (actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ)) r 0 1 * D r) :=
      (intervalIntegral.integral_const_mul _ _).symm
    _ = ∫ r in (0 : ℝ)..s,
        ((Real.exp (-2*Y*(t-s)) : ℂ) * complexRealOscillatoryPhase35 (-2*x) s*star (U s)) *
        (U r * (complexRealOscillatoryPhase35 (2*x) r*((Real.exp (-2*Y*r) : ℂ) * D r))) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have h := actualInteractionPair11_phaseRescaling35 U x Y t s r
      calc
        _ = ((Real.exp (-2*Y*t) : ℂ) *
            (actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ)) s 1 0 *
              actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ)) r 0 1)) * D r := by ring
        _ = ((Real.exp (-2*Y*(t-s)) : ℂ) * complexRealOscillatoryPhase35 (-2*x) s *
      star (U s) * U r * complexRealOscillatoryPhase35 (2*x) r *
              (Real.exp (-2*Y*r) : ℂ)) * D r := by rw [h]
        _ = _ := by ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]

end NlsGge.SpectralFoundations
end
