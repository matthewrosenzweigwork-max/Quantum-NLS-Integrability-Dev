import NlsGge.Spectral.ActualPhysicalInteractionGaugeAEODE32V2
import NlsGge.Spectral.ActualPhysicalUnitDiscriminantNonrealZeroFree32V1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Exact actual unit-trace rescaling. The 11 interaction contribution
carries exp(-2Y), whereas the 00 contribution is unweighted. This is an
algebraic identity, not a tail or asymptotic assumption. -/
theorem actualPhysicalUnitHalfTrace_verticalRescaling33
    (u : PhysicalL2) (Y : ℝ) :
    (Real.exp (-Y) : ℂ)*actualPhysicalUnitHalfTrace32 u (Complex.I*(Y : ℂ)) =
      (actualZsInteractionState32 (Complex.I*(Y : ℂ))
        (actualComplexZsDysonTsum
          (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
          (Complex.I*(Y : ℂ))) 1 0 0 +
        (Real.exp (-2*Y) : ℂ)*actualZsInteractionState32 (Complex.I*(Y : ℂ))
        (actualComplexZsDysonTsum
          (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
          (Complex.I*(Y : ℂ))) 1 1 1)/2 := by
  have h0 : actualZsInverseFreeWeight32 (Complex.I*(Y : ℂ)) 1 0 =
      (Real.exp (-Y) : ℂ) := by
    rw [actualZsInverseFreeWeight32, one_smul, Complex.ofReal_exp]
    congr 1
    simp only [actualZsFreeRate32, if_pos rfl]
    ring_nf
    simp
  have h1 : actualZsInverseFreeWeight32 (Complex.I*(Y : ℂ)) 1 1 =
      (Real.exp Y : ℂ) := by
    rw [actualZsInverseFreeWeight32, one_smul, Complex.ofReal_exp]
    congr 1
    simp only [actualZsFreeRate32, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    ring_nf
    simp
  have hfactor : (Real.exp (-2*Y) : ℂ)*(Real.exp Y : ℂ) =
      (Real.exp (-Y) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  simp only [actualPhysicalUnitHalfTrace32, Matrix.trace_fin_two,
    actualZsInteractionState32, h0, h1]
  calc
    _ = ((Real.exp (-Y) : ℂ)*
          actualComplexZsDysonTsum
            (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
            (Complex.I*(Y : ℂ)) 1 0 0 +
        ((Real.exp (-2*Y) : ℂ)*(Real.exp Y : ℂ))*
          actualComplexZsDysonTsum
            (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
            (Complex.I*(Y : ℂ)) 1 1 1)/2 := by rw [hfactor]; ring
    _ = _ := by ring

end NlsGge.SpectralFoundations
end
