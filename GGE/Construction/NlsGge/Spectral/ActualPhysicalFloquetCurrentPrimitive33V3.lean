import NlsGge.Spectral.ActualPhysicalFloquetStateACAE33V3
import NlsGge.Spectral.ActualZsIndefiniteCurrentAlgebra33V2
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The genuine indefinite current of the actual rough source state is AC. -/
theorem actualPhysicalFloquetCurrent_AC33
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) :
    AbsolutelyContinuousOnInterval
      (fun t => actualZsIndefiniteCurrent33 (actualPhysicalFloquetState33 u z v t)) 0 2 := by
  have h0 := actualPhysicalFloquetState_AC33 u z v 0
  have h1 := actualPhysicalFloquetState_AC33 u z v 1
  have hs0 := (star_isometry (E := ℂ)).lipschitz.comp_absolutelyContinuousOnInterval h0
  have hs1 := (star_isometry (E := ℂ)).lipschitz.comp_absolutelyContinuousOnInterval h1
  simpa only [actualZsIndefiniteCurrent33, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
    Function.comp_apply] using! (h0.smul hs0).sub (h1.smul hs1)

/-- Exact AE Green-current identity for the actual rough source flow. -/
theorem actualPhysicalFloquetCurrent_ae_hasDerivAt33
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 2 →
      HasDerivAt
        (fun s => actualZsIndefiniteCurrent33 (actualPhysicalFloquetState33 u z v s))
        (((2*z.im : ℝ) : ℂ) *
          (actualPhysicalFloquetState33 u z v t 0 * star (actualPhysicalFloquetState33 u z v t 0) +
           actualPhysicalFloquetState33 u z v t 1 * star (actualPhysicalFloquetState33 u z v t 1))) t := by
  filter_upwards [actualPhysicalFloquetState_ae_hasDerivAt33 u z v 0,
    actualPhysicalFloquetState_ae_hasDerivAt33 u z v 1] with t h0 h1
  intro ht
  have h := ((h0 ht).mul (h0 ht).star).sub ((h1 ht).mul (h1 ht).star)
  have ha := actualZsIndefiniteCurrent_derivative_algebra33
    (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
    z t (actualPhysicalFloquetState33 u z v t)
  dsimp only at ha
  rw [ha] at h
  simpa only [actualZsIndefiniteCurrent33] using! h

/-- The current's derivative is continuous after the exact cancellation,
so its integral is realized without any pointwise regularity of the field. -/
theorem actualPhysicalFloquetCurrent_primitive33
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    actualZsIndefiniteCurrent33 (actualPhysicalFloquetState33 u z v t) =
      actualZsIndefiniteCurrent33 v +
        ∫ s in (0 : ℝ)..t, ((2*z.im : ℝ) : ℂ) *
          (actualPhysicalFloquetState33 u z v s 0 * star (actualPhysicalFloquetState33 u z v s 0) +
           actualPhysicalFloquetState33 u z v s 1 * star (actualPhysicalFloquetState33 u z v s 1)) := by
  have hc (i : Fin 2) : ContinuousOn (fun s => actualPhysicalFloquetState33 u z v s i)
      (Set.Icc (0 : ℝ) 2) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using
      (actualPhysicalFloquetState_AC33 u z v i).continuousOn
  have hg : IntervalIntegrable
      (fun s => ((2*z.im : ℝ) : ℂ) *
        (actualPhysicalFloquetState33 u z v s 0 * star (actualPhysicalFloquetState33 u z v s 0) +
         actualPhysicalFloquetState33 u z v s 1 * star (actualPhysicalFloquetState33 u z v s 1)))
      volume 0 2 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 2)
    exact continuousOn_const.mul (((hc 0).mul (hc 0).star).add ((hc 1).mul (hc 1).star))
  have hp := complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt
    (actualPhysicalFloquetCurrent_AC33 u z v) hg
    (actualPhysicalFloquetCurrent_ae_hasDerivAt33 u z v)
  have htu : t ∈ Set.uIcc (0 : ℝ) 2 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  simpa only [actualPhysicalFloquetState_initial33] using! hp t htu

end NlsGge.SpectralFoundations
end
