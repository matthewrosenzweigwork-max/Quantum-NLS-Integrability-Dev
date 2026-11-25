import QuantumNLS.TerraMultiRound65FirstIBP

/-! Second periodic integration-by-parts identity in the REG-008 proof. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open QuantumNLS.ClassicalCharges QuantumNLS.WeakDerivatives
open QuantumNLS.TerraMultiRound65PeriodicIBP
namespace QuantumNLS.TerraMultiRound65SecondIBP

theorem second_integration_by_parts (L : ℝ) {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    (∫ x in (0 : ℝ)..L, -(conj (f x))^2 * f x * deriv (deriv f) x) =
      ∫ x in (0 : ℝ)..L, 2 * ((‖f x‖^2 * ‖deriv f x‖^2 : ℝ) : ℂ) +
        (conj (f x))^2 * (deriv f x)^2 := by
  have hs1 := (contDiff_infty_iff_deriv.mp hf.smooth).2
  have hdiff := (contDiff_infty_iff_deriv.mp hf.smooth).1
  have hdiff1 := (contDiff_infty_iff_deriv.mp hs1).1
  have hA (x : ℝ) : deriv (fun y => (conj (f y))^2 * f y) x =
      (2 * conj (f x) * conj (deriv f x)) * f x + (conj (f x))^2 * deriv f x := by
    have hd := (hdiff x).hasDerivAt
    have he := (hd.star.pow 2).mul hd
    change HasDerivAt (fun y => (conj (f y))^2 * f y) _ x at he
    convert he.deriv using 1 <;> simp [RCLike.star_def] <;> ring
  have p1 : Function.Periodic (fun y => (conj (f y))^2 * f y) L := by
    intro y
    change (conj (f (y + L)))^2 * f (y + L) = (conj (f y))^2 * f y
    rw [hf.periodic y]
  have p2 : Function.Periodic (deriv f) L := periodic_deriv hf.periodic
  have s1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (conj (f y))^2 * f y) := by
    exact ((Complex.conjCLE.contDiff.comp hf.smooth).pow 2).mul hf.smooth
  have hp := periodic_integration_by_parts L _ _ s1 hs1 p1 p2
  calc
    _ = -(∫ x in (0 : ℝ)..L, ((conj (f x))^2 * f x) * deriv (deriv f) x) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      ring
    _ = ∫ x in (0 : ℝ)..L, deriv (fun y => (conj (f y))^2 * f y) x * deriv f x := by
      rw [hp, neg_neg]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [hA]
      have hz : conj (f x) * f x = ((‖f x‖^2 : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      have hw : conj (deriv f x) * deriv f x = ((‖deriv f x‖^2 : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast at hz hw ⊢
      rw [← hz, ← hw]
      ring

#print axioms second_integration_by_parts
end QuantumNLS.TerraMultiRound65SecondIBP
