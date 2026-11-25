import QuantumNLS.TerraMultiRound64ExtendedIdentity

/-! The extended real moment is the actual nonnegative extended integral. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.TerraMultiRound64ExtendedIdentity
namespace QuantumNLS.TerraMultiRound64ExtendedMeasure

def ennrealToWithTop (a : ℝ≥0∞) : WithTop ℝ := by
  classical
  exact if a = ⊤ then ⊤ else ↑a.toReal

theorem extended_moment_eq_lintegral (μ : Measure ℝ) (s : ℕ) :
    extendedEvenMoment μ s = ennrealToWithTop (∫⁻ t : ℝ, ENNReal.ofReal (t^(2*s)) ∂μ) := by
  classical
  have hm : AEStronglyMeasurable (fun t : ℝ => t^(2*s)) μ :=
    (by fun_prop : Continuous (fun t : ℝ => t^(2*s))).aestronglyMeasurable
  have hn : ∀ᵐ t ∂μ, 0 ≤ t^(2*s) := ae_of_all _ ((even_two_mul s).pow_nonneg)
  have hi := lintegral_ofReal_ne_top_iff_integrable hm hn
  by_cases hf : Integrable (fun t : ℝ => t^(2*s)) μ
  · have htop := hi.mpr hf
    rw [extendedEvenMoment, if_pos hf, ennrealToWithTop, if_neg htop]
    rw [← ofReal_integral_eq_lintegral_ofReal hf hn, ENNReal.toReal_ofReal]
    exact integral_nonneg ((even_two_mul s).pow_nonneg)
  · have htop : (∫⁻ t : ℝ, ENNReal.ofReal (t^(2*s)) ∂μ) = ⊤ := by
      by_contra h
      exact hf (hi.mp h)
    simp [extendedEvenMoment, ennrealToWithTop, hf, htop]

#print axioms extended_moment_eq_lintegral
end QuantumNLS.TerraMultiRound64ExtendedMeasure
