import NlsGge.Spectral.ActualInteractionPairKernel32V2
import NlsGge.Spectral.ComplexRealOscillatoryPhase35V1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations

/-- Opposite-channel phase factor, with its growing height exponent retained. -/
theorem complexUpperHalfPlaneOppositePairExponential_phaseFactor35
    (x Y s r : ℝ) :
    Complex.exp (-2*Complex.I*((x : ℂ)+Complex.I*(Y : ℂ))*((s-r : ℝ) : ℂ)) =
      (Real.exp (2*Y*(s-r)) : ℂ)*
        complexRealOscillatoryPhase35 (-2*x) s*
        complexRealOscillatoryPhase35 (2*x) r := by
  have hparam : ((-x : ℝ) : ℂ)+Complex.I*((-Y : ℝ) : ℂ) =
      -((x : ℂ)+Complex.I*(Y : ℂ)) := by push_cast; ring
  have h := complexUpperHalfPlanePairExponential_phaseFactor35 (-x) (-Y) s r
  rw [hparam] at h
  have he1 : -2*(-Y)*(s-r) = 2*Y*(s-r) := by ring
  have he2 : 2*(-x) = -2*x := by ring
  have he3 : -2*(-x) = 2*x := by ring
  rw [he1, he2, he3] at h
  convert h using 1
  congr 1
  ring

end NlsGge.SpectralFoundations
end
