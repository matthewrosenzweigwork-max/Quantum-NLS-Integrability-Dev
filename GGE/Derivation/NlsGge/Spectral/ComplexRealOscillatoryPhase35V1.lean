import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations

def complexRealOscillatoryPhase35 (ω t : ℝ) : ℂ :=
  Complex.exp (Complex.I*(ω : ℂ)*(t : ℂ))

/-- Actual real-frequency phases have exactly unit norm. -/
theorem complexRealOscillatoryPhase_norm35 (ω t : ℝ) :
    ‖complexRealOscillatoryPhase35 ω t‖ = 1 := by
  simp [complexRealOscillatoryPhase35, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- No rough-field regularity is used to establish phase continuity. -/
theorem complexRealOscillatoryPhase_continuous35 (ω : ℝ) :
    Continuous (complexRealOscillatoryPhase35 ω) := by
  unfold complexRealOscillatoryPhase35
  fun_prop

/-- The actual complex pair-kernel exponential separates its height decay
and two norm-one oscillatory phases, preserving the source factor2. -/
theorem complexUpperHalfPlanePairExponential_phaseFactor35 (x Y s r : ℝ) :
    Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*(Y : ℂ))*((s-r : ℝ) : ℂ)) =
      (Real.exp (-2*Y*(s-r)) : ℂ)*
        complexRealOscillatoryPhase35 (2*x) s*
        complexRealOscillatoryPhase35 (-2*x) r := by
  unfold complexRealOscillatoryPhase35
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

end NlsGge.SpectralFoundations
end
