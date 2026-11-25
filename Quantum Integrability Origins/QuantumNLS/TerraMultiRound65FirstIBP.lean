import QuantumNLS.TerraMultiRound65PeriodicIBP
import QuantumNLS.WeakDerivatives

/-! First of the two periodic integration-by-parts identities in REG-008. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open QuantumNLS.ClassicalCharges QuantumNLS.WeakDerivatives
open QuantumNLS.TerraMultiRound65PeriodicIBP
namespace QuantumNLS.TerraMultiRound65FirstIBP

theorem first_integration_by_parts (L : ℝ) {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    (∫ x in (0 : ℝ)..L, -conj (f x) * conj (deriv (deriv f) x) * f x^2) =
      ∫ x in (0 : ℝ)..L, f x^2 * (conj (deriv f x))^2 +
        2 * ((‖f x‖^2 * ‖deriv f x‖^2 : ℝ) : ℂ) := by
  have hs1 := (contDiff_infty_iff_deriv.mp hf.smooth).2
  have hdiff := (contDiff_infty_iff_deriv.mp hf.smooth).1
  have hdiff1 := (contDiff_infty_iff_deriv.mp hs1).1
  have hA (x : ℝ) : deriv (fun y => conj (f y) * f y^2) x =
      conj (deriv f x) * f x^2 + conj (f x) * (2 * f x * deriv f x) := by
    have hd := (hdiff x).hasDerivAt
    have he := hd.star.mul (hd.pow 2)
    change HasDerivAt (fun y => conj (f y) * f y^2) _ x at he
    convert he.deriv using 1 <;> simp [RCLike.star_def] <;> ring
  have hB (x : ℝ) : deriv (fun y => conj (deriv f y)) x = conj (deriv (deriv f) x) := by
    exact (hdiff1 x).hasDerivAt.star.deriv
  have p1 : Function.Periodic (fun y => conj (f y) * f y^2) L := by
    intro y
    change conj (f (y + L)) * f (y + L)^2 = conj (f y) * f y^2
    rw [hf.periodic y]
  have p2 : Function.Periodic (fun y => conj (deriv f y)) L := by
    intro y
    change conj (deriv f (y + L)) = conj (deriv f y)
    rw [periodic_deriv hf.periodic y]
  have s1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => conj (f y) * f y^2) := by
    exact (Complex.conjCLE.contDiff.comp hf.smooth).mul (hf.smooth.pow 2)
  have s2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => conj (deriv f y)) := by
    exact Complex.conjCLE.contDiff.comp hs1
  have hp := periodic_integration_by_parts L _ _ s1 s2 p1 p2
  calc
    _ = -(∫ x in (0 : ℝ)..L, (conj (f x) * f x^2) *
        deriv (fun y => conj (deriv f y)) x) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [hB]
      ring
    _ = ∫ x in (0 : ℝ)..L, deriv (fun y => conj (f y) * f y^2) x * conj (deriv f x) := by rw [hp, neg_neg]
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

#print axioms first_integration_by_parts
end QuantumNLS.TerraMultiRound65FirstIBP
