import Mathlib

/- G2-032 B4 (proof development, AUTHOR; SUPPORTING lemma, not a packet; NOT self-reviewed). Mathlib-only.
   Arcsine substitution t = cos θ on the θ-period, with evenness θ ↦ 2π − θ:
   (N1) integrability of F(t)/√(1−t²) on [−1,1] for F continuous on [−1,1];
   (N2) ∫_0^{2π} F(cos θ) dθ = 2 ∫_{−1}^{1} F(t)/√(1−t²) dt.
   Here √(1−t²) is the real square root cast to ℂ, as in `rescaledActionIntegrand`. -/
set_option autoImplicit false

open Set MeasureTheory
open scoped Real

namespace NlsGge.GKDefinitionDesign
namespace G2032Arcsine
noncomputable section

theorem image_cos_Ioo_eq : Real.cos '' Ioo 0 π = Ioo (-1) 1 := by
  rw [ContinuousOn.image_Ioo_of_strictAntiOn Real.pi_pos.le Real.continuous_cos.continuousOn
    Real.strictAntiOn_cos]
  simp

theorem sqrt_one_sub_cos_sq (θ : ℝ) (h0 : 0 < θ) (hπ : θ < π) :
    Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ := by
  have h : 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 := by rw [Real.sin_sq]
  rw [h]
  exact Real.sqrt_sq (Real.sin_pos_of_pos_of_lt_pi h0 hπ).le

/-- Pointwise identity on (0, π): the integrand is the θ-weight times the arcsine integrand. -/
theorem pointwise_identity (F : ℝ → ℂ) (θ : ℝ) (h0 : 0 < θ) (hπ : θ < π) :
    F (Real.cos θ) = |-Real.sin θ| •
      (F (Real.cos θ) / ((Real.sqrt (1 - Real.cos θ ^ 2) : ℝ) : ℂ)) := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hs : ((Real.sin θ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsin.ne'
  rw [sqrt_one_sub_cos_sq θ h0 hπ, abs_neg, abs_of_pos hsin, Complex.real_smul]
  field_simp

theorem integral_Ioo_cos (F : ℝ → ℂ) :
    ∫ θ in Ioo (0 : ℝ) π, F (Real.cos θ) =
      ∫ x in Ioo (-1 : ℝ) 1, F x / ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) := by
  have hinj : InjOn Real.cos (Ioo 0 π) := Real.injOn_cos.mono Ioo_subset_Icc_self
  have hf' : ∀ x ∈ Ioo (0 : ℝ) π, HasDerivWithinAt Real.cos (-Real.sin x) (Ioo 0 π) x :=
    fun x _ => (Real.hasDerivAt_cos x).hasDerivWithinAt
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hf' hinj
    (fun x : ℝ => F x / ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ))
  rw [image_cos_Ioo_eq] at hchange
  rw [hchange]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ hθ
  exact pointwise_identity F θ hθ.1 hθ.2

theorem integral_two_pi_eq (F : ℝ → ℂ) (hF : ContinuousOn F (Icc (-1) 1)) :
    ∫ θ in (0 : ℝ)..(2 * π), F (Real.cos θ) = 2 * ∫ θ in (0 : ℝ)..π, F (Real.cos θ) := by
  have hcont : Continuous (fun θ : ℝ => F (Real.cos θ)) :=
    hF.comp_continuous Real.continuous_cos
      (fun θ => ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
  have h2 : ∫ θ in π..(2 * π), F (Real.cos θ) = ∫ θ in (0 : ℝ)..π, F (Real.cos θ) := by
    have h : ∫ x in (0 : ℝ)..π, (fun θ => F (Real.cos θ)) (2 * π - x) =
        ∫ x in 2 * π - π..2 * π - 0, F (Real.cos x) :=
      intervalIntegral.integral_comp_sub_left (f := fun θ => F (Real.cos θ)) (2 * π)
    simp only [Real.cos_two_pi_sub] at h
    rw [show 2 * π - π = π by ring, show 2 * π - 0 = 2 * π by ring] at h
    exact h.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 π)
    (hcont.intervalIntegrable π (2 * π)), h2]
  ring

theorem arcsine_substitution (F : ℝ → ℂ) (hF : ContinuousOn F (Icc (-1) 1)) :
    (∫ θ in (0 : ℝ)..(2 * π), F (Real.cos θ)) =
      2 * ∫ t in (-1 : ℝ)..1, F t / ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ) := by
  rw [integral_two_pi_eq F hF, intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, integral_Ioo_cos F]

theorem arcsine_intervalIntegrable (F : ℝ → ℂ) (hF : ContinuousOn F (Icc (-1) 1)) :
    IntervalIntegrable (fun t : ℝ => F t / ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ))
      volume (-1) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integrableOn_Ioc_iff_integrableOn_Ioo]
  have hinj : InjOn Real.cos (Ioo 0 π) := Real.injOn_cos.mono Ioo_subset_Icc_self
  have hf' : ∀ x ∈ Ioo (0 : ℝ) π, HasDerivWithinAt Real.cos (-Real.sin x) (Ioo 0 π) x :=
    fun x _ => (Real.hasDerivAt_cos x).hasDerivWithinAt
  have hcont : ContinuousOn (fun θ : ℝ => F (Real.cos θ)) (Icc 0 π) :=
    (hF.comp_continuous Real.continuous_cos
      (fun θ => ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)).continuousOn
  rw [← image_cos_Ioo_eq, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    hf' hinj]
  apply IntegrableOn.congr_fun (f := fun θ : ℝ => F (Real.cos θ))
  · exact (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  · intro θ hθ
    exact pointwise_identity F θ hθ.1 hθ.2
  · exact measurableSet_Ioo

end
end G2032Arcsine
end NlsGge.GKDefinitionDesign
