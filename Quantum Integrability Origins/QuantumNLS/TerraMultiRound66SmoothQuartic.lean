import QuantumNLS.TerraMultiRound65SecondIBP
import QuantumNLS.TerraMultiRound65DensityDerivative

/-! Combination of the two integrations by parts in the smooth fourth moment. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open QuantumNLS.ClassicalCharges
open QuantumNLS.TerraMultiRound65FirstIBP QuantumNLS.TerraMultiRound65SecondIBP
open QuantumNLS.TerraMultiRound65DensityDerivative
namespace QuantumNLS.TerraMultiRound66SmoothQuartic

theorem smooth_quartic_integral (L : ℝ) {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    (∫ x in (0 : ℝ)..L,
      -conj (f x) * conj (deriv (deriv f) x) * f x^2
      - 6 * conj (f x) * conj (deriv f x) * f x * deriv f x
      - 5 * (conj (f x))^2 * (deriv f x)^2
      - 6 * (conj (f x))^2 * f x * deriv (deriv f) x) =
    ∫ x in (0 : ℝ)..L,
      6 * ((‖f x‖^2 * ‖deriv f x‖^2 : ℝ) : ℂ) +
      (deriv (fun y => ((‖f y‖^2 : ℝ) : ℂ)) x)^2 := by
  let A : ℝ → ℂ := fun x => -conj (f x) * conj (deriv (deriv f) x) * f x^2
  let B : ℝ → ℂ := fun x => -(conj (f x))^2 * f x * deriv (deriv f) x
  let C : ℝ → ℂ := fun x => ((‖f x‖^2 * ‖deriv f x‖^2 : ℝ) : ℂ)
  let D : ℝ → ℂ := fun x => f x^2 * (conj (deriv f x))^2
  let E : ℝ → ℂ := fun x => (conj (f x))^2 * (deriv f x)^2
  have cf : Continuous f := hf.smooth.continuous
  have cf' : Continuous (deriv f) := (contDiff_infty_iff_deriv.mp hf.smooth).2.continuous
  have cf'' : Continuous (deriv (deriv f)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf.smooth).2).2.continuous
  have hA : IntervalIntegrable A volume 0 L := by apply Continuous.intervalIntegrable; dsimp [A]; fun_prop
  have hB : IntervalIntegrable B volume 0 L := by apply Continuous.intervalIntegrable; dsimp [B]; fun_prop
  have hC : IntervalIntegrable C volume 0 L := by apply Continuous.intervalIntegrable; dsimp [C]; fun_prop
  have hD : IntervalIntegrable D volume 0 L := by apply Continuous.intervalIntegrable; dsimp [D]; fun_prop
  have hE : IntervalIntegrable E volume 0 L := by apply Continuous.intervalIntegrable; dsimp [E]; fun_prop
  have h₁ : (∫ x in (0 : ℝ)..L, A x) = ∫ x in (0 : ℝ)..L, D x + 2 * C x :=
    first_integration_by_parts L hf
  have h₂ : (∫ x in (0 : ℝ)..L, B x) = ∫ x in (0 : ℝ)..L, 2 * C x + E x :=
    second_integration_by_parts L hf
  rw [intervalIntegral.integral_add hD (hC.const_mul 2), intervalIntegral.integral_const_mul] at h₁
  rw [intervalIntegral.integral_add (hC.const_mul 2) hE, intervalIntegral.integral_const_mul] at h₂
  calc
    _ = ∫ x in (0 : ℝ)..L, A x + 6 * B x - 6 * C x - 5 * E x := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp [A, B, C, E]
      have hz : conj (f x) * f x = ((‖f x‖^2 : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      have hw : conj (deriv f x) * deriv f x = ((‖deriv f x‖^2 : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast at hz hw ⊢
      rw [← hz, ← hw]
      ring
    _ = ∫ x in (0 : ℝ)..L, D x + 8 * C x + E x := by
      rw [intervalIntegral.integral_sub ((hA.add (hB.const_mul 6)).sub (hC.const_mul 6)) (hE.const_mul 5),
        intervalIntegral.integral_sub (hA.add (hB.const_mul 6)) (hC.const_mul 6),
        intervalIntegral.integral_add hA (hB.const_mul 6),
        intervalIntegral.integral_add (hD.add (hC.const_mul 8)) hE,
        intervalIntegral.integral_add hD (hC.const_mul 8)]
      simp only [intervalIntegral.integral_const_mul]
      linear_combination h₁ + 6 * h₂
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact correction_at_point ((contDiff_infty_iff_deriv.mp hf.smooth).1 x)

#print axioms smooth_quartic_integral
end QuantumNLS.TerraMultiRound66SmoothQuartic
