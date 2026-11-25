import Mathlib

/- KSN018 PURE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN018Pure.lean.
   SUPPORT (no packet increment) for KSN-018: the pure complex algebra of Pro's route (round 15 Q5, L858) at one label.
   With s = smoothingCoefficient, the Cartesian identity (KSN-010 + cartZ) reads
     s = ξ·e·((τ−μ) − a·i·A·δ⁻¹/2)·η + G,  τ−μ = E₁ − (F₁+F₂)/2,  A = i·σ·(F₁−F₂) + E₂,  G = (F₁+F₂)/2 − a(F₁−F₂)/2,
   σ = (−1)ⁿ (σ² = 1), a = ±1. Then s = (ξeη − 1)(−G) + ξeη·R with R = E₁ − a·i·E₂·δ⁻¹/2 + a·σ·(F₁−F₂)(δ⁻¹−σ)/2, so
   if |ξ−1|, |e−1|, |η−1|, |δ⁻¹−σ| ≤ K/w (w ≥ 1):
     w^{N+1}|s| ≤ Kc·(wᴺ|F₁| + wᴺ|F₂| + w^{N+1}|E₁| + w^{N+1}|E₂|),  Kc explicit in K.
   Also |exp z − 1| ≤ (2 + exp c)·t for |z| ≤ t ≤ c. Mathlib only; no hypothesis added. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSN018P
noncomputable section

theorem exp_sub_one_le (z : ℂ) (t c : ℝ) (hzt : ‖z‖ ≤ t) (htc : t ≤ c) :
    ‖Complex.exp z - 1‖ ≤ (2 + Real.exp c) * t := by
  have ht0 : 0 ≤ t := (norm_nonneg _).trans hzt
  have hec : 0 < Real.exp c := Real.exp_pos c
  by_cases h1 : ‖z‖ ≤ 1
  · have := Complex.norm_exp_sub_one_le h1
    nlinarith
  · push_neg at h1
    have hexp : ‖Complex.exp z‖ ≤ Real.exp c := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.2 ((Complex.re_le_norm z).trans (hzt.trans htc))
    have h2 : ‖Complex.exp z - 1‖ ≤ Real.exp c + 1 := by
      have := norm_sub_le (Complex.exp z) 1
      rw [norm_one] at this
      linarith
    have ht1 : 1 ≤ t := by linarith
    nlinarith

theorem exp_norm_le (z : ℂ) (c : ℝ) (hz : ‖z‖ ≤ c) : ‖Complex.exp z‖ ≤ Real.exp c := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.2 ((Complex.re_le_norm z).trans hz)

theorem split_identity (s ξ e η di τμ A G E1 E2 F1 F2 σ a : ℂ)
    (hs : s = ξ * e * ((τμ - a * Complex.I * A * di / 2) * η) + G)
    (hτμ : τμ = E1 - (F1 + F2) / 2) (hA : A = Complex.I * σ * (F1 - F2) + E2)
    (hG : G = (F1 + F2) / 2 - a * (F1 - F2) / 2) (hσ2 : σ ^ 2 = 1) :
    s = (ξ * e * η - 1) * (-G) +
      ξ * e * η * (E1 - a * Complex.I * E2 * di / 2 + a * σ * (F1 - F2) * (di - σ) / 2) := by
  rw [hs, hτμ, hA, hG]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (ξ * e * η * a * (F1 - F2) / 2) * hσ2 + (ξ * e * a * σ * di * η * (F2 - F1) / 2) * hI

theorem s_norm_bound (N : ℕ) (w K : ℝ) (hw : 1 ≤ w) (hK : 0 ≤ K)
    (s ξ e η di τμ A G E1 E2 F1 F2 σ a : ℂ)
    (hs : s = ξ * e * ((τμ - a * Complex.I * A * di / 2) * η) + G)
    (hτμ : τμ = E1 - (F1 + F2) / 2) (hA : A = Complex.I * σ * (F1 - F2) + E2)
    (hG : G = (F1 + F2) / 2 - a * (F1 - F2) / 2) (hσ2 : σ ^ 2 = 1) (hσ : ‖σ‖ = 1) (ha : ‖a‖ = 1)
    (hξ : ‖ξ - 1‖ ≤ K / w) (he : ‖e - 1‖ ≤ K / w) (hη : ‖η - 1‖ ≤ K / w) (hd : ‖di - σ‖ ≤ K / w) :
    ‖s‖ ≤ 3 * (1 + K) ^ 2 * (K / w) * (‖F1‖ + ‖F2‖) +
      (1 + K) ^ 3 * (‖E1‖ + (1 + K) * ‖E2‖ + (K / w) * (‖F1‖ + ‖F2‖)) := by
  have hw0 : 0 < w := by linarith
  have hKw : K / w ≤ K := div_le_self hK hw
  have hKw0 : 0 ≤ K / w := by positivity
  have hsplit := split_identity s ξ e η di τμ A G E1 E2 F1 F2 σ a hs hτμ hA hG hσ2
  -- elementary bounds
  have nb : ∀ z : ℂ, ‖z - 1‖ ≤ K / w → ‖z‖ ≤ 1 + K := fun z hz => by
    have := norm_le_norm_add_norm_sub' z 1
    have h1 : ‖z‖ ≤ ‖(1 : ℂ)‖ + ‖z - 1‖ := by
      have := norm_add_le (1 : ℂ) (z - 1); simpa using this
    rw [norm_one] at h1; linarith
  have hξn := nb ξ hξ
  have hen := nb e he
  have hηn := nb η hη
  have hdin : ‖di‖ ≤ 1 + K := by
    have h1 : ‖di‖ ≤ ‖σ‖ + ‖di - σ‖ := by
      have := norm_add_le σ (di - σ); simpa using this
    rw [hσ] at h1; linarith
  have hK1 : 0 ≤ 1 + K := by linarith
  have hprod : ‖ξ * e * η‖ ≤ (1 + K) ^ 3 := by
    rw [norm_mul, norm_mul]
    have := mul_le_mul (mul_le_mul hξn hen (norm_nonneg _) hK1) hηn (norm_nonneg _) (by positivity)
    nlinarith
  have hprod1 : ‖ξ * e * η - 1‖ ≤ 3 * (1 + K) ^ 2 * (K / w) := by
    have e1 : ξ * e * η - 1 = (ξ - 1) * e * η + (e - 1) * η + (η - 1) := by ring
    rw [e1]
    have t1 : ‖(ξ - 1) * e * η‖ ≤ (K / w) * (1 + K) * (1 + K) := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hξ hen (norm_nonneg _) hKw0) hηn (norm_nonneg _) (by positivity)
    have t2 : ‖(e - 1) * η‖ ≤ (K / w) * (1 + K) := by
      rw [norm_mul]; exact mul_le_mul he hηn (norm_nonneg _) hKw0
    have a1 := norm_add_le ((ξ - 1) * e * η + (e - 1) * η) (η - 1)
    have a2 := norm_add_le ((ξ - 1) * e * η) ((e - 1) * η)
    have hK1' : 1 ≤ 1 + K := by linarith
    have q1 : (K / w) * (1 + K) ≤ (K / w) * (1 + K) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hKw0; nlinarith
    have q2 : K / w ≤ (K / w) * (1 + K) ^ 2 := by
      have : 1 ≤ (1 + K) ^ 2 := by nlinarith
      nlinarith
    have q3 : (K / w) * (1 + K) * (1 + K) = (K / w) * (1 + K) ^ 2 := by ring
    have q4 : 3 * (1 + K) ^ 2 * (K / w) = (K / w) * (1 + K) ^ 2 * 3 := by ring
    rw [q4]
    linarith
  have hG1 : ‖G‖ ≤ ‖F1‖ + ‖F2‖ := by
    rw [hG]
    have e1 : (F1 + F2) / 2 - a * (F1 - F2) / 2 = ((1 - a) / 2) * F1 + ((1 + a) / 2) * F2 := by ring
    rw [e1]
    have b1 : ‖(1 - a) / 2‖ ≤ 1 := by
      rw [norm_div, Complex.norm_ofNat]
      have := norm_sub_le (1 : ℂ) a; rw [norm_one, ha] at this; linarith
    have b2 : ‖(1 + a) / 2‖ ≤ 1 := by
      rw [norm_div, Complex.norm_ofNat]
      have := norm_add_le (1 : ℂ) a; rw [norm_one, ha] at this; linarith
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have := mul_le_mul_of_nonneg_right b1 (norm_nonneg F1)
    have := mul_le_mul_of_nonneg_right b2 (norm_nonneg F2)
    linarith
  set R : ℂ := E1 - a * Complex.I * E2 * di / 2 + a * σ * (F1 - F2) * (di - σ) / 2 with hR
  have hRn : ‖R‖ ≤ ‖E1‖ + (1 + K) * ‖E2‖ + (K / w) * (‖F1‖ + ‖F2‖) := by
    have r1 : ‖a * Complex.I * E2 * di / 2‖ ≤ (1 + K) * ‖E2‖ := by
      rw [norm_div, norm_mul, norm_mul, norm_mul, ha, Complex.norm_I, Complex.norm_ofNat]
      have := mul_le_mul_of_nonneg_left hdin (norm_nonneg E2)
      nlinarith [norm_nonneg E2, norm_nonneg di]
    have r2 : ‖a * σ * (F1 - F2) * (di - σ) / 2‖ ≤ (K / w) * (‖F1‖ + ‖F2‖) := by
      rw [norm_div, norm_mul, norm_mul, norm_mul, ha, hσ, Complex.norm_ofNat]
      have f1 := norm_sub_le F1 F2
      have := mul_le_mul f1 hd (norm_nonneg _) (by positivity)
      nlinarith [norm_nonneg (F1 - F2), norm_nonneg (di - σ)]
    have := norm_add_le (E1 - a * Complex.I * E2 * di / 2) (a * σ * (F1 - F2) * (di - σ) / 2)
    have := norm_sub_le E1 (a * Complex.I * E2 * di / 2)
    linarith
  -- assemble
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_neg]
  have p1 := mul_le_mul hprod1 hG1 (norm_nonneg _) (by positivity)
  have p2 := mul_le_mul hprod hRn (norm_nonneg _) (by positivity)
  linarith

theorem pure_coeff (N : ℕ) (w K : ℝ) (hw : 1 ≤ w) (hK : 0 ≤ K)
    (s ξ e η di τμ A G E1 E2 F1 F2 σ a : ℂ)
    (hs : s = ξ * e * ((τμ - a * Complex.I * A * di / 2) * η) + G)
    (hτμ : τμ = E1 - (F1 + F2) / 2) (hA : A = Complex.I * σ * (F1 - F2) + E2)
    (hG : G = (F1 + F2) / 2 - a * (F1 - F2) / 2) (hσ2 : σ ^ 2 = 1) (hσ : ‖σ‖ = 1) (ha : ‖a‖ = 1)
    (hξ : ‖ξ - 1‖ ≤ K / w) (he : ‖e - 1‖ ≤ K / w) (hη : ‖η - 1‖ ≤ K / w) (hd : ‖di - σ‖ ≤ K / w) :
    w ^ (N + 1) * ‖s‖ ≤ (4 * (1 + K) ^ 4 * (1 + K)) *
      (w ^ N * ‖F1‖ + w ^ N * ‖F2‖ + w ^ (N + 1) * ‖E1‖ + w ^ (N + 1) * ‖E2‖) := by
  have hsn := s_norm_bound N w K hw hK s ξ e η di τμ A G E1 E2 F1 F2 σ a hs hτμ hA hG hσ2 hσ ha hξ he hη hd
  have hw0 : 0 < w := by linarith
  have hK1 : 0 ≤ 1 + K := by linarith
  set P : ℝ := ‖F1‖ + ‖F2‖ with hP
  have hP0 : 0 ≤ P := by positivity
  have hwN : 0 < w ^ N := pow_pos hw0 N
  have hw1 : w ^ (N + 1) = w ^ N * w := pow_succ w N
  have key : w ^ (N + 1) * ‖s‖ ≤ w ^ N * (3 * (1 + K) ^ 2 * K * P + (1 + K) ^ 3 * K * P) +
      (1 + K) ^ 3 * (w ^ (N + 1) * ‖E1‖ + (1 + K) * (w ^ (N + 1) * ‖E2‖)) := by
    have h1 := mul_le_mul_of_nonneg_left hsn (le_of_lt (pow_pos hw0 (N + 1)))
    refine h1.trans (le_of_eq ?_)
    rw [hw1]
    field_simp
    ring
  have hA0 : 0 ≤ w ^ N * ‖F1‖ := by positivity
  have hB0 : 0 ≤ w ^ N * ‖F2‖ := by positivity
  have hC0 : 0 ≤ w ^ (N + 1) * ‖E1‖ := by positivity
  have hD0 : 0 ≤ w ^ (N + 1) * ‖E2‖ := by positivity
  have hc1 : 3 * (1 + K) ^ 2 * K + (1 + K) ^ 3 * K ≤ 4 * (1 + K) ^ 4 * (1 + K) := by
    have h1 : K ≤ 1 + K := by linarith
    have h2 : (1 + K) ^ 2 ≤ (1 + K) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h3 : (1 + K) ^ 3 ≤ (1 + K) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith [mul_le_mul h2 h1 hK (by positivity), mul_le_mul h3 h1 hK (by positivity)]
  have hc2 : (1 + K) ^ 3 ≤ 4 * (1 + K) ^ 4 * (1 + K) := by
    have h3 : (1 + K) ^ 3 ≤ (1 + K) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  have hc3 : (1 + K) ^ 3 * (1 + K) ≤ 4 * (1 + K) ^ 4 * (1 + K) := by nlinarith [pow_nonneg hK1 4]
  have e1 : w ^ N * (3 * (1 + K) ^ 2 * K * P + (1 + K) ^ 3 * K * P) =
      (3 * (1 + K) ^ 2 * K + (1 + K) ^ 3 * K) * (w ^ N * ‖F1‖ + w ^ N * ‖F2‖) := by rw [hP]; ring
  rw [e1] at key
  have m1 := mul_le_mul_of_nonneg_right hc1 (add_nonneg hA0 hB0)
  have m2 := mul_le_mul_of_nonneg_right hc2 hC0
  have m3 := mul_le_mul_of_nonneg_right hc3 hD0
  have e2 : (1 + K) ^ 3 * (w ^ (N + 1) * ‖E1‖ + (1 + K) * (w ^ (N + 1) * ‖E2‖)) =
      (1 + K) ^ 3 * (w ^ (N + 1) * ‖E1‖) + (1 + K) ^ 3 * (1 + K) * (w ^ (N + 1) * ‖E2‖) := by ring
  have e3 : (4 * (1 + K) ^ 4 * (1 + K)) *
      (w ^ N * ‖F1‖ + w ^ N * ‖F2‖ + w ^ (N + 1) * ‖E1‖ + w ^ (N + 1) * ‖E2‖) =
      (4 * (1 + K) ^ 4 * (1 + K)) * (w ^ N * ‖F1‖ + w ^ N * ‖F2‖) +
      (4 * (1 + K) ^ 4 * (1 + K)) * (w ^ (N + 1) * ‖E1‖) +
      (4 * (1 + K) ^ 4 * (1 + K)) * (w ^ (N + 1) * ‖E2‖) := by ring
  rw [e2] at key
  rw [e3]
  linarith

end
end NlsGge.ThirdConsultation.KSN018P
