import NlsGge.Spectral.ActualPhysicalFloquetCurrentPrimitive33V3
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Every genuine unit-modulus Floquet multiplier of the actual rough
period-one source monodromy has real spectral parameter. This includes all
phases; no parity-only reduction or real-field hypothesis is made. -/
theorem actualPhysicalUnitFloquetMultiplier_im_eq_zero33
    (u : PhysicalL2) (z χ : ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0)
    (hχ : ‖χ‖ = 1)
    (heigen : (actualComplexZsDysonTsum
      (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
      z 1).mulVec v = χ • v) : z.im = 0 := by
  have hcurrent (w : Fin 2 → ℂ) : actualZsIndefiniteCurrent33 w =
      ((‖w 0‖ ^ 2 - ‖w 1‖ ^ 2 : ℝ) : ℂ) := by
    simp only [actualZsIndefiniteCurrent33, Complex.star_def, Complex.mul_conj',
      Complex.ofReal_sub, Complex.ofReal_pow]
  have hstate : actualPhysicalFloquetState33 u z v 1 = χ • v := heigen
  have hend : actualZsIndefiniteCurrent33 (actualPhysicalFloquetState33 u z v 1) =
      actualZsIndefiniteCurrent33 v := by
    rw [hstate, hcurrent, hcurrent]
    congr 1
    simpa only [Pi.smul_apply, smul_eq_mul] using
      actualZsUnitScalar_preserves_realCurrent33 χ hχ v
  have hp := actualPhysicalFloquetCurrent_primitive33 u z v 1 (by norm_num)
  rw [hend] at hp
  have hzero : (∫ s in (0 : ℝ)..1, ((2*z.im : ℝ) : ℂ) *
      (actualPhysicalFloquetState33 u z v s 0 * star (actualPhysicalFloquetState33 u z v s 0) +
       actualPhysicalFloquetState33 u z v s 1 * star (actualPhysicalFloquetState33 u z v s 1))) = 0 := by
    have h := congrArg (fun w : ℂ => w - actualZsIndefiniteCurrent33 v) hp
    simpa only [sub_self, add_sub_cancel_left] using h.symm
  rw [intervalIntegral.integral_const_mul] at hzero
  have he (s : ℝ) :
      actualPhysicalFloquetState33 u z v s 0 * star (actualPhysicalFloquetState33 u z v s 0) +
      actualPhysicalFloquetState33 u z v s 1 * star (actualPhysicalFloquetState33 u z v s 1) =
      ((‖actualPhysicalFloquetState33 u z v s 0‖ ^ 2 +
        ‖actualPhysicalFloquetState33 u z v s 1‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.star_def, Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_pow]
  simp_rw [he] at hzero
  rw [intervalIntegral.integral_ofReal] at hzero
  have hpos := actualPhysicalFloquet_energy_integral_pos33 u z v hv
  have hnonzero : ((∫ s in (0 : ℝ)..1,
      ‖actualPhysicalFloquetState33 u z v s 0‖ ^ 2 +
      ‖actualPhysicalFloquetState33 u z v s 1‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  have hz : ((2*z.im : ℝ) : ℂ) = 0 := (mul_eq_zero.mp hzero).resolve_right hnonzero
  have hzreal : 2*z.im = 0 := by exact_mod_cast hz
  nlinarith

/-- Nonreal parameters exclude every unit-modulus eigenmultiplier of the
actual original period-one monodromy. -/
theorem actualPhysicalNonreal_noUnitFloquetMultiplier33
    (u : PhysicalL2) (z χ : ℂ) (hz : z.im ≠ 0) (hχ : ‖χ‖ = 1) :
    ¬ ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      (actualComplexZsDysonTsum
        (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
        z 1).mulVec v = χ • v := by
  rintro ⟨v, hv, heigen⟩
  exact hz (actualPhysicalUnitFloquetMultiplier_im_eq_zero33 u z χ v hv hχ heigen)

end NlsGge.SpectralFoundations
end
