import NlsGge.Atomic.M.M037
import NlsGge.Atomic.M.M006
import NlsGge.ThirdConsultation.M.M038Norm
import NlsGge.ThirdConsultation.M.M038Absorb

/- proof development M038 PRODUCTION01 (AUTHOR; not self-reviewed; not accepted). Target NlsGge/Atomic/M/M038.lean,
   namespace NlsGge.ThirdConsultation.M. Head VERBATIM from STATEMENTS/M.md (M-038, followup4 = followup5; no later
   Pro head). Degree bound for the support of normalizedChargeRemainder is derived (M004 grading + weight identity),
   not assumed. Supports: M038Norm (Sobolev norm comparison), M038Absorb (AM-GM absorption). -/
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.Atomic.Common
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.M

theorem m038_fieldCount_le (m : ℕ) (hm : 1 ≤ m) (q : Jet →₀ ℕ)
    (hq : q ∈ (normalizedChargeRemainder m).support) : fieldCount q ≤ 2 * m + 2 := by
  have hw : riccatiJetWeightHomAfterComponents q = 2 * m + 2 :=
    (riccati_normalized_remainder_monomial_grading m hm q hq).1
  have hs := riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery q
  have hd := NlsGge.ThirdConsultation.M.M004Aux.fieldCount_eq_degree q
  omega

theorem m038_chargeBounds (m : ℕ) (hm : 1 ≤ m) (q : Jet →₀ ℕ)
    (hq : q ∈ (normalizedChargeRemainder m).support) : ChargeMonomialBounds m q := by
  obtain ⟨-, hg, -, h4, hord, -, hv⟩ := riccati_normalized_remainder_monomial_grading m hm q hq
  exact ⟨h4, hg, hord, hv⟩

theorem m038_four_le (m : ℕ) (hm : 1 ≤ m) (q : Jet →₀ ℕ)
    (hq : q ∈ (normalizedChargeRemainder m).support) : 4 ≤ fieldCount q :=
  (riccati_normalized_remainder_monomial_grading m hm q hq).2.2.2.1

theorem charge_remainder_absorption
    (m : ℕ) (hm : 1 ≤ m) (eps : ℝ) (heps : 0 < eps) :
  ∃ C : ℝ, 0 < C ∧ ∀ u : SobolevR m,
    |chargeRemainder m u| ≤
      eps * topDerivativeNorm m u^2 +
      C * (1+‖physicalOfSobolev u‖^(4*m)) *
        ‖physicalOfSobolev u‖^2 := by
  classical
  obtain ⟨K, hK0, hK⟩ := NlsGge.ThirdConsultation.M.M038Norm.norm_sq_le m
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpos2m : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hinv : 2 * (m : ℝ) * (2 * (m : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hpos2m.ne'
  obtain ⟨sE, hsE⟩ : ∃ f : (Jet →₀ ℕ) → ℝ,
      ∀ q, f q = ((fieldCount q : ℝ) - 2) / (2 * (m : ℝ)) :=
    ⟨fun q => ((fieldCount q : ℝ) - 2) / (2 * (m : ℝ)), fun q => rfl⟩
  have hM : ∀ q ∈ (normalizedChargeRemainder m).support, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevR m,
      ‖integralMonomial q u‖ ≤
        C * (‖u‖ ^ (2 - sE q) * ‖physicalOfSobolev u‖ ^ ((2 * (m : ℝ) + 1) * sE q)) := by
    intro q hq
    obtain ⟨C, hC0, hC⟩ := hierarchy_monomial_subquadratic m hm q
      (m038_chargeBounds m hm q hq) (m038_fieldCount_le m hm q hq)
    refine ⟨C, hC0, fun u => ?_⟩
    have e1 : 2 - ((fieldCount q : ℝ) - 2) / (2 * (m : ℝ)) = 2 - sE q := by
      rw [hsE q]
    have e2 : (1 + 1 / (2 * (m : ℝ))) * ((fieldCount q : ℝ) - 2) =
        (2 * (m : ℝ) + 1) * sE q := by
      rw [hsE q]
      linear_combination (-((fieldCount q : ℝ) - 2)) * hinv
    have hu := hC u
    rw [e1, e2] at hu
    exact hu.trans (le_of_eq (mul_assoc _ _ _))
  have hs0 : ∀ q ∈ (normalizedChargeRemainder m).support, 0 < sE q := by
    intro q hq
    have h4 : (4 : ℝ) ≤ (fieldCount q : ℝ) := by exact_mod_cast m038_four_le m hm q hq
    rw [hsE q]
    exact div_pos (by linarith) hpos2m
  have hs1 : ∀ q ∈ (normalizedChargeRemainder m).support, sE q ≤ 1 := by
    intro q hq
    have hr : (fieldCount q : ℝ) ≤ 2 * (m : ℝ) + 2 := by
      exact_mod_cast m038_fieldCount_le m hm q hq
    rw [hsE q]
    exact (div_le_one hpos2m).2 (by linarith)
  choose! Cf hCf0 hCf using hM
  obtain ⟨κ, hκdef⟩ : ∃ κ : (Jet →₀ ℕ) → ℝ, ∀ q,
      κ q = |(((normalizedChargeRemainder m).coeff q : ℤ) : ℝ)| * Cf q := ⟨_, fun q => rfl⟩
  have hκ0 : ∀ q ∈ (normalizedChargeRemainder m).support, 0 ≤ κ q := by
    intro q hq
    rw [hκdef]
    exact mul_nonneg (abs_nonneg _) (hCf0 q hq)
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ,
      η = eps / (K * (((normalizedChargeRemainder m).support.card : ℝ) + 1)) := ⟨_, rfl⟩
  have hc1 : ((normalizedChargeRemainder m).support.card : ℝ) + 1 ≠ 0 := by positivity
  have hKne : K ≠ 0 := hK0.ne'
  have hη : 0 < η := by
    rw [hηdef]
    exact div_pos heps (mul_pos hK0 (by positivity))
  have hηK : η * K * (((normalizedChargeRemainder m).support.card : ℝ) + 1) = eps := by
    rw [hηdef, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hKne hc1)]
    ring
  obtain ⟨D, hD0, hDsum⟩ := NlsGge.ThirdConsultation.M.M038Absorb.young_sum m
    (normalizedChargeRemainder m).support sE κ hκ0 hs0 hs1 η hη
  have hcK : ((normalizedChargeRemainder m).support.card : ℝ) * η * K ≤ eps := by
    have hηK0 : 0 ≤ η * K := mul_nonneg hη.le hK0.le
    have hc : ((normalizedChargeRemainder m).support.card : ℝ) ≤
        ((normalizedChargeRemainder m).support.card : ℝ) + 1 := by linarith
    calc ((normalizedChargeRemainder m).support.card : ℝ) * η * K
        = ((normalizedChargeRemainder m).support.card : ℝ) * (η * K) := by ring
      _ ≤ (((normalizedChargeRemainder m).support.card : ℝ) + 1) * (η * K) :=
          mul_le_mul_of_nonneg_right hc hηK0
      _ = eps := by rw [← hηK]; ring
  refine ⟨eps + D + 1, by linarith, fun u => ?_⟩
  have hcr : chargeRemainder m u = normalizedRemainderIntegral m u := by
    unfold chargeRemainder signedCharge
    ring
  have hB1 : |normalizedRemainderIntegral m u| ≤
      ∑ q ∈ (normalizedChargeRemainder m).support, κ q *
        (‖u‖ ^ (2 - sE q) * ‖physicalOfSobolev u‖ ^ ((2 * (m : ℝ) + 1) * sE q)) := by
    unfold normalizedRemainderIntegral
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q hq => ?_)
    show |(((normalizedChargeRemainder m).coeff q : ℤ) : ℝ) * (integralMonomial q u).re| ≤
      κ q * (‖u‖ ^ (2 - sE q) * ‖physicalOfSobolev u‖ ^ ((2 * (m : ℝ) + 1) * sE q))
    rw [abs_mul, hκdef]
    calc |(((normalizedChargeRemainder m).coeff q : ℤ) : ℝ)| * |(integralMonomial q u).re|
        ≤ |(((normalizedChargeRemainder m).coeff q : ℤ) : ℝ)| * ‖integralMonomial q u‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
      _ ≤ |(((normalizedChargeRemainder m).coeff q : ℤ) : ℝ)| *
            (Cf q * (‖u‖ ^ (2 - sE q) * ‖physicalOfSobolev u‖ ^ ((2 * (m : ℝ) + 1) * sE q))) :=
          mul_le_mul_of_nonneg_left (hCf q hq u) (abs_nonneg _)
      _ = |(((normalizedChargeRemainder m).coeff q : ℤ) : ℝ)| * Cf q *
            (‖u‖ ^ (2 - sE q) * ‖physicalOfSobolev u‖ ^ ((2 * (m : ℝ) + 1) * sE q)) := by ring
  have hB2 := hDsum ‖u‖ ‖physicalOfSobolev u‖ (norm_nonneg _) (norm_nonneg _)
  have hcrb : |chargeRemainder m u| ≤
      ((normalizedChargeRemainder m).support.card : ℝ) * (η * ‖u‖ ^ 2) +
        D * ‖physicalOfSobolev u‖ ^ (4 * m + 2) := by
    rw [hcr]
    exact hB1.trans hB2
  have hN := hK u
  have hstep : ((normalizedChargeRemainder m).support.card : ℝ) * (η * ‖u‖ ^ 2) ≤
      eps * (topDerivativeNorm m u ^ 2 + ‖physicalOfSobolev u‖ ^ 2) := by
    calc ((normalizedChargeRemainder m).support.card : ℝ) * (η * ‖u‖ ^ 2)
        = ((normalizedChargeRemainder m).support.card : ℝ) * η * ‖u‖ ^ 2 := by ring
      _ ≤ ((normalizedChargeRemainder m).support.card : ℝ) * η *
            (K * (topDerivativeNorm m u ^ 2 + ‖physicalOfSobolev u‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hN (mul_nonneg (Nat.cast_nonneg _) hη.le)
      _ = ((normalizedChargeRemainder m).support.card : ℝ) * η * K *
            (topDerivativeNorm m u ^ 2 + ‖physicalOfSobolev u‖ ^ 2) := by ring
      _ ≤ eps * (topDerivativeNorm m u ^ 2 + ‖physicalOfSobolev u‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hcK (by positivity)
  have hB4 : ‖physicalOfSobolev u‖ ^ (4 * m + 2) =
      ‖physicalOfSobolev u‖ ^ (4 * m) * ‖physicalOfSobolev u‖ ^ 2 := pow_add _ _ _
  have hBp : 0 ≤ ‖physicalOfSobolev u‖ ^ (4 * m) := pow_nonneg (norm_nonneg _) _
  have hB2' : 0 ≤ ‖physicalOfSobolev u‖ ^ 2 := sq_nonneg _
  have hBB : 0 ≤ ‖physicalOfSobolev u‖ ^ (4 * m) * ‖physicalOfSobolev u‖ ^ 2 :=
    mul_nonneg hBp hB2'
  rw [hB4] at hcrb
  nlinarith [hcrb, hstep, mul_nonneg hD0 hB2', mul_nonneg heps.le hBB, hBB, hB2']

end NlsGge.ThirdConsultation.M
