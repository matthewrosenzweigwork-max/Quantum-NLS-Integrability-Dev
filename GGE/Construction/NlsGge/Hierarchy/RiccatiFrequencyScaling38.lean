import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

open scoped ContDiff

namespace NlsGge.HierarchyRiccati.Core

/-- Iterated derivatives of a frequency-scaled smooth function: `∂ʸ^m (f (k y)) = k^m f^(m) (k y)`. -/
theorem iteratedDeriv_comp_mul38 (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (k : ℝ) (m : ℕ) (x : ℝ) :
    iteratedDeriv m (fun y => f (k * y)) x = k ^ m * iteratedDeriv m f (k * x) := by
  have h : ContDiff ℝ (m : WithTop ℕ∞) f := hf.of_le (by exact_mod_cast le_top)
  exact congrFun (iteratedDeriv_comp_const_mul h k) x

/-- Frequency scaling by a positive integer preserves the unit period. -/
theorem periodic_comp_nat_mul38 (f : ℝ → ℝ) (hper : Function.Periodic f 1) (k : ℕ) :
    Function.Periodic (fun y => f (k * y)) 1 := by
  intro y
  have h := (hper.nat_mul k) (k * y)
  simpa [mul_add] using h

/-- The unit-interval mean of a continuous `1`-periodic function is invariant under frequency
scaling by a positive integer. -/
theorem intervalIntegral_comp_nat_mul_periodic38 (h : ℝ → ℝ) (hc : Continuous h)
    (hper : Function.Periodic h 1) (k : ℕ) (hk : 1 ≤ k) :
    (∫ x in (0:ℝ)..1, h (k * x)) = ∫ x in (0:ℝ)..1, h x := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hint : ∀ t₁ t₂, IntervalIntegrable h MeasureTheory.volume t₁ t₂ :=
    fun t₁ t₂ => hc.intervalIntegrable t₁ t₂
  have hsm := hper.intervalIntegral_add_zsmul_eq (k : ℤ) 0 hint
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one] at hsm
  rw [intervalIntegral.integral_comp_mul_left (fun x => h x) hk0]
  simp only [mul_zero, mul_one, smul_eq_mul]
  rw [hsm]
  field_simp


end NlsGge.HierarchyRiccati.Core
