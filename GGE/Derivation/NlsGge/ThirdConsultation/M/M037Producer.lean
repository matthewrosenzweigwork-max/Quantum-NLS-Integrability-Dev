import NlsGge.Atomic.M.M005

/- proof development M037Producer (SUPPORTING for the M-037 head 2; AUTHOR; not reviewed).
   Head 2 of M-037 (PRO_DEFINITION_RESPONSE_FP80_07_08.md §17): the M-005 integration-by-parts normal form
   terms (the support of normalizedChargeRemainder m, with its coefficients) satisfy the field-degree bound.
   The ChargeNormalForm conjuncts are the M-005 proof of hierarchy_IBP_normal_form, copied verbatim (proof only).
   The degree bound uses the weighted grading: weight = 2m+2 (riccati_normalized_remainder_monomial_grading),
   weight = degree + derivative order sum in ℕ (no truncation), so degree ≤ 2m+2. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.M.M037Producer

open MeasureTheory
open NlsGge.HierarchyRiccati.Core

theorem image_normalForm_degree (m : ℕ) (hm : 1 ≤ m) :
    ∃ terms : Finset ((NlsGge.HierarchyRiccati.Core.Jet →₀ ℕ) × ℤ),
      ChargeNormalForm m terms ∧ ∀ t ∈ terms, fieldCount t.1 ≤ 2 * m + 2 := by
  classical
  refine ⟨(normalizedChargeRemainder m).support.image
    (fun q => (q, (normalizedChargeRemainder m).coeff q)), ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨-, hg, -, h4, hord, -, hv⟩ := riccati_normalized_remainder_monomial_grading m hm q hq
    exact ⟨h4, hg, hord, hv⟩
  · intro u hu hper
    have h1 : (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalChargeIntegrand m)) =
        (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalChargeQuadraticMainTerm m)) +
        (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (normalizedChargeRemainder m)) :=
      formalChargeIntegrand_integral_quadratic_plus_uniformRemainderNativeRecovery29Fourth
        m u hu hper
    have h2 := formalChargeQuadraticMainTerm_integral_eq38 m u hu hper
    have h3 : (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (normalizedChargeRemainder m)) =
        ∑ q ∈ (normalizedChargeRemainder m).support,
          (((normalizedChargeRemainder m).coeff q : ℤ) : ℂ) *
            ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (MvPolynomial.monomial q (1 : ℤ)) := by
      conv_lhs => rw [(normalizedChargeRemainder m).as_sum]
      rw [riccatiJetEvaluation_integral_finset_sumNativeRecoverySecond u hu]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      have : ∀ x : ℝ, riccatiJetEvaluation u x
          (MvPolynomial.monomial q ((normalizedChargeRemainder m).coeff q)) =
          (((normalizedChargeRemainder m).coeff q : ℤ) : ℂ) *
            riccatiJetEvaluation u x (MvPolynomial.monomial q (1 : ℤ)) := by
        intro x
        have hmon : MvPolynomial.monomial q ((normalizedChargeRemainder m).coeff q) =
            MvPolynomial.C ((normalizedChargeRemainder m).coeff q) *
              MvPolynomial.monomial q (1 : ℤ) := by
          rw [MvPolynomial.C_mul_monomial, mul_one]
        rw [hmon]
        simp [riccatiJetEvaluation, polynomialEvaluation, map_mul]
      simp_rw [this]
      exact intervalIntegral.integral_const_mul _ _
    unfold smoothSignedCharge smoothTopDerivativeEnergy smoothIntegralMonomial
    rw [h1, h2, h3, intervalIntegral.integral_ofReal, Finset.sum_image (by
      intro a _ b _ hab; exact (Prod.mk.inj hab).1)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl (fun q _ => ?_)
    simp [Complex.mul_re]
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
    have hw : riccatiJetWeightHomAfterComponents q = 2 * m + 2 :=
      (riccati_normalized_remainder_monomial_grading m hm q hq).1
    have hs := riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery q
    have hd := NlsGge.ThirdConsultation.M.M004Aux.fieldCount_eq_degree q
    show fieldCount q ≤ 2 * m + 2
    omega

end NlsGge.ThirdConsultation.M.M037Producer
