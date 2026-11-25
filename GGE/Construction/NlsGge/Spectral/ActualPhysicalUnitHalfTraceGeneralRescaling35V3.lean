import NlsGge.Spectral.ActualPhysicalUnitVerticalTraceRescaling33V2
import NlsGge.Spectral.ComplexRealOscillatoryPhase35V1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual half trace after removal of its growing free factor, at EVERY complex
parameter. This exact algebra identity preserves the opposite-channel phase. -/
theorem actualPhysicalUnitHalfTrace_generalRescaling35
    (u : PhysicalL2) (z : ℂ) :
    Complex.exp (Complex.I*z)*actualPhysicalUnitHalfTrace32 u z =
      (actualZsInteractionState32 z
        (actualComplexZsDysonTsum
          (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) z) 1 0 0 +
        Complex.exp (2*Complex.I*z)*actualZsInteractionState32 z
        (actualComplexZsDysonTsum
          (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) z) 1 1 1)/2 := by
  have h0 : actualZsInverseFreeWeight32 z 1 0 = Complex.exp (Complex.I*z) := by
    simp only [actualZsInverseFreeWeight32, one_smul, actualZsFreeRate32, if_pos rfl, ite_true]
    congr 1
    ring
  have h1 : actualZsInverseFreeWeight32 z 1 1 = Complex.exp (-Complex.I*z) := by
    simp only [actualZsInverseFreeWeight32, one_smul, actualZsFreeRate32,
      if_neg (by decide : (1 : Fin 2) ≠ 0)]
    congr 1
    ring
  have hfactor : Complex.exp (2*Complex.I*z)*Complex.exp (-Complex.I*z) =
      Complex.exp (Complex.I*z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [actualPhysicalUnitHalfTrace32, Matrix.trace_fin_two,
    actualZsInteractionState32, h0, h1]
  calc
    _ = (Complex.exp (Complex.I*z)*actualComplexZsDysonTsum
          (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) z 1 0 0 +
        (Complex.exp (2*Complex.I*z)*Complex.exp (-Complex.I*z))*
          actualComplexZsDysonTsum
            (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) z 1 1 1)/2 := by
      rw [hfactor]
      ring
    _ = _ := by ring

/-- The opposite-channel factor has exactly a unit-modulus real-frequency phase
and height damping. This does not discard the phase or assert trace reality. -/
theorem complexDoubledUpperHalfPlaneExponential_phase35 (x Y : ℝ) :
    Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*(Y : ℂ))) =
      complexRealOscillatoryPhase35 (2*x) 1*(Real.exp (-2*Y) : ℂ) := by
  rw [complexRealOscillatoryPhase35, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  simp [sub_eq_add_neg]

end NlsGge.SpectralFoundations
end
