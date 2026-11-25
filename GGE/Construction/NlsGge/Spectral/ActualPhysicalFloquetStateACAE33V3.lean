import NlsGge.Spectral.ActualPhysicalFloquetEnergyPositive33V2
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Actual finite-coordinate flow retains the initial vector. -/
theorem actualPhysicalFloquetState_initial33
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) :
    actualPhysicalFloquetState33 u z v 0 = v := by
  unfold actualPhysicalFloquetState33
  rw [(actualPhysicalL2ZsDysonTsum_is_AC_fundamental u z).1]
  simp

/-- The actual rough source state is AC on the complete doubled interval. -/
theorem actualPhysicalFloquetState_AC33
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) (i : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t => actualPhysicalFloquetState33 u z v t i) 0 2 := by
  have h0 := absolutelyContinuous_actualPhysicalL2ZsDysonTsum_entry u z i 0
  have h1 := absolutelyContinuous_actualPhysicalL2ZsDysonTsum_entry u z i 1
  have a := h0.const_smul (v 0)
  have b := h1.const_smul (v 1)
  simpa only [actualPhysicalFloquetState33, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Pi.add_apply, smul_eq_mul, mul_comm] using! a.add b

/-- AE differentiation of the actual source state, with the genuine
complex U/starU coefficient. No continuous-field representative is assumed. -/
theorem actualPhysicalFloquetState_ae_hasDerivAt33
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) (i : Fin 2) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 2 →
      HasDerivAt (fun s => actualPhysicalFloquetState33 u z v s i)
        ((zsCoefficientComplex
          (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
          z t).mulVec (actualPhysicalFloquetState33 u z v t) i) t := by
  filter_upwards [actualPhysicalL2ZsDysonTsum_ae_hasDerivAt_entry u z i 0,
    actualPhysicalL2ZsDysonTsum_ae_hasDerivAt_entry u z i 1] with t h0 h1
  intro ht
  have h := ((h0 ht).mul_const (v 0)).add ((h1 ht).mul_const (v 1))
  unfold actualPhysicalFloquetState33
  rw [Matrix.mulVec_mulVec]
  simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply] using! h

end NlsGge.SpectralFoundations
end
