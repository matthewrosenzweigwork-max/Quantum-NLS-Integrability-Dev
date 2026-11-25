import NlsGge.Sobolev.SmoothFourier
import NlsGge.Hierarchy.RiccatiPeriodicIteratedDerivClosurePrerequisite
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot
open MeasureTheory
open scoped ContDiff Interval

/-- One integration-by-parts step for the actual period-one Fourier coefficient.
The hypotheses are a smooth real-line representative and its genuine period-one
identity; the conclusion is the physical multiplier `2π i n`. -/
theorem riccatiFourierCoeffOn_deriv_periodOneRecovery29
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (n : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (deriv u) n =
      fourierMultiplier n * fourierCoeffOn (by norm_num : (0 : ℝ) < 1) u n := by
  let h01 : (0 : ℝ) < 1 := by norm_num
  have hderiv : ∀ x, HasDerivAt u (deriv u x) x := by
    intro x
    exact ((hu.differentiable (by simp)).differentiableAt).hasDerivAt
  have hderivCont : Continuous (deriv u) := hu.continuous_deriv (by simp)
  have hderivInt : IntervalIntegrable (deriv u) volume 0 1 :=
    hderivCont.intervalIntegrable 0 1
  have hendpoint : u 1 = u 0 := by
    simpa using hper 0
  by_cases hn : n = 0
  · subst n
    rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
    have hFTC : ∫ x in (0 : ℝ)..1, deriv u x = u 1 - u 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hderiv x) hderivInt
    have hmult0 : fourierMultiplier (0 : ℤ) = 0 := by simp [fourierMultiplier]
    simp [hendpoint, hFTC, hmult0]
  · have hparts := fourierCoeffOn_of_hasDerivAt_Ioo h01 hn
      (hu.continuous.continuousOn)
      (fun x _ => hderiv x)
      hderivInt
    rw [hendpoint] at hparts
    simp only [sub_self, mul_zero, zero_sub, one_mul] at hparts
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hden : (-2 * Real.pi * Complex.I * (n : ℂ)) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) hnC
    have hmul : fourierMultiplier n = -( -2 * Real.pi * Complex.I * (n : ℂ)) := by
      simp [fourierMultiplier]
    have hidentity : fourierCoeffOn h01 (deriv u) n =
        fourierMultiplier n * fourierCoeffOn h01 u n := by
      rw [hmul]
      field_simp [hden] at hparts ⊢
      simpa [mul_comm, mul_left_comm, mul_assoc] using hparts.symm
    exact hidentity

/-- Repeated classical differentiation multiplies the actual period-one
Fourier coefficient by the corresponding power of the physical multiplier. -/
theorem riccatiFourierCoeffOn_iteratedDeriv_periodOneRecovery29
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (k : ℕ) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (iteratedDeriv k u) n =
      fourierMultiplier n ^ k *
        fourierCoeffOn (by norm_num : (0 : ℝ) < 1) u n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hsmooth : ContDiff ℝ ∞ (iteratedDeriv k u) := by
        rw [iteratedDeriv_eq_iterate]
        exact ContDiff.iterate_deriv k hu
      have hperiodic :=
        NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff u hu hper k
      rw [riccatiFourierCoeffOn_deriv_periodOneRecovery29
        (iteratedDeriv k u) hsmooth hperiodic n, ih]
      rw [pow_succ]
      ring

end NlsGge.HierarchyRiccati.Core

end
