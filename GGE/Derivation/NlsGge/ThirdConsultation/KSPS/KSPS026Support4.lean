import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS026Support3
import NlsGge.GK38.PairAnalyticDet

/- KSPS-026 SUPPORT4 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS026Support4.lean.
   KSPS-026 step 3 (KSPS026_MAP01.md; source KST proof of Thm 1.2, (37)-(40)):
   * `periodic_disc_sq`: Δ(λ±_n)^2 = 4 (lamSeq_enumeration38, perChar = Δ^2 - 4);
   * `disc_sign_eventually`: for a sample sequence xi localized near n π with Δ(xi n)^2 = 4 and the KSPS-015 weighted l2
     conclusion Δ(xi n) - 2 cos θ(xi n), eventually Δ(xi n) = 2 (-1)^n (θ = n π + t, |t| <= (a + Σ|I_k|)/w, and
     |Δ - 2(-1)^n| <= 3 < 4 excludes the root -2(-1)^n);
   * `quad_alg`: with s = ±1, η = s e^{iθ} (s e_f = η^-1, s e_t = η), the exact entries of M = D^-1 W1 adj W0
     (KSPS015Support.explicit_formula), det M = 1 and tr M = 2s give q0 η^2 + q1 η + q2 = 0, because
     η D det(sM - 1) = q0 η^2 + q1 η + q2 identically and det(sM - 1) = s^2 det M - s tr M + 1 = 0;
   * `quad_zero_at`: the concrete instance for scaledEndpointCorrection / endpointQuadraticABC.
   The KSPS-013/014 head conclusions enter as explicit hypotheses of exactly their landed types. -/
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS026W
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS015W NlsGge.ThirdConsultation.KSPS016W

/-! ### Periodic eigenvalues -/

theorem periodic_disc_sq {N : ℕ} (φ : SobolevC N) (n : ℤ) :
    NlsGge.ThirdConsultation.KSPS.discriminant φ (periodicPlus φ n) ^ 2 = 4 ∧
    NlsGge.ThirdConsultation.KSPS.discriminant φ (periodicMinus φ n) ^ 2 = 4 := by
  have hp := (lamSeq_enumeration38 (toPotPair φ)).1 (2 * n + 1)
  have hm := (lamSeq_enumeration38 (toPotPair φ)).1 (2 * n)
  rw [perChar_eq] at hp hm
  exact ⟨sub_eq_zero.mp hp, sub_eq_zero.mp hm⟩

/-! ### Elementary cosine facts (re-proved locally) -/

theorem norm_cos_sub_one_le' {t : ℂ} (ht : ‖t‖ ≤ 1) : ‖Complex.cos t - 1‖ ≤ ‖t‖ ^ 2 := by
  have h1 : ‖Complex.exp (-t * Complex.I) - 1 - (-t * Complex.I)‖ ≤ ‖t‖ ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le (x := -t * Complex.I) (by simpa using ht)
    simpa using this
  have h2 : ‖Complex.exp (t * Complex.I) - 1 - (t * Complex.I)‖ ≤ ‖t‖ ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le (x := t * Complex.I) (by simpa using ht)
    simpa using this
  have key : Complex.cos t - 1 =
      ((Complex.exp (-t * Complex.I) - 1 - (-t * Complex.I)) +
        (Complex.exp (t * Complex.I) - 1 - (t * Complex.I))) / 2 := by
    rw [Complex.cos]; ring
  rw [key, norm_div, Complex.norm_ofNat]
  have := norm_add_le (Complex.exp (-t * Complex.I) - 1 - (-t * Complex.I))
    (Complex.exp (t * Complex.I) - 1 - (t * Complex.I))
  linarith

theorem cos_int_mul_pi_add' (n : ℤ) (t : ℂ) :
    Complex.cos ((n : ℂ) * (Real.pi : ℂ) + t) = (-1 : ℂ) ^ n * Complex.cos t := by
  have hc : Complex.cos ((n : ℂ) * (Real.pi : ℂ)) = (-1 : ℂ) ^ n := by
    have h := Complex.ofReal_cos ((n : ℝ) * Real.pi)
    rw [Real.cos_int_mul_pi] at h
    push_cast at h
    exact h.symm
  rw [Complex.cos_add, Complex.sin_int_mul_pi, zero_mul, sub_zero, hc]

theorem abs_le_indexWeight (n : ℤ) : |(n : ℝ)| ≤ indexWeight n := by
  unfold indexWeight
  rw [Real.le_sqrt (abs_nonneg _) (by positivity), sq_abs]
  linarith

/-! ### The phase correction is O(1/|lam|) -/

/-- Literal abbreviation: the sum of the moduli of the Riccati integrals I_1, ..., I_N. -/
def CI {N : ℕ} (φ : SobolevC N) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, ‖integralRiccatiLeft φ k‖

theorem CI_nonneg {N : ℕ} (φ : SobolevC N) : 0 ≤ CI φ :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem phase_sum_le {N : ℕ} (φ : SobolevC N) (lam : ℂ) (h : 1 ≤ 2 * ‖lam‖) :
    ‖∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ * integralRiccatiLeft φ k‖ ≤
      CI φ / (2 * ‖lam‖) := by
  have h0 : 0 < 2 * ‖lam‖ := by linarith
  refine (norm_sum_le _ _).trans ?_
  unfold CI
  rw [Finset.sum_div]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
  rw [norm_mul, norm_inv, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  have hp : 2 * ‖lam‖ ≤ (2 * ‖lam‖) ^ k := by
    calc 2 * ‖lam‖ = (2 * ‖lam‖) ^ 1 := (pow_one _).symm
      _ ≤ (2 * ‖lam‖) ^ k := pow_le_pow_right₀ h hk1
  rw [mul_comm, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (norm_nonneg _) h0 hp

/-! ### The sign of the discriminant at the endpoints -/

theorem disc_sign_eventually (N : ℕ) (φ : SobolevC N) (xi : ℤ → ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hroot : ∀ n : ℤ, NlsGge.ThirdConsultation.KSPS.discriminant φ (xi n) ^ 2 = 4)
    (h15 : WeightedL2Error ((N + 1 : ℕ) : ℝ)
      (fun n : ℤ => NlsGge.ThirdConsultation.KSPS.discriminant φ (xi n) -
        2 * Complex.cos (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n)))) :
    ∀ᶠ n : ℤ in cofinite, NlsGge.ThirdConsultation.KSPS.discriminant φ (xi n) = 2 * (-1 : ℂ) ^ n := by
  have hw := one_le_indexWeight'
  have hL2 := ((weightedL2Error_iff N _).1 h15).mono hw (Nat.zero_le _)
  have hsmall := hL2.eventually_le hw 1 one_pos
  filter_upwards [hsmall, eventually_natAbs (⌈a⌉₊ + ⌈a + CI φ⌉₊ + 1)] with n hd hn
  simp only [pow_zero, one_mul] at hd
  obtain ⟨hX1, hXT, hwX⟩ := tail_facts a (a + CI φ) ha xi hxi n hn
  -- the phase deviation t
  set t : ℂ := NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) - (n : ℂ) * (Real.pi : ℂ) with htdef
  have hw0 : 0 < indexWeight n := lt_of_lt_of_le one_pos (one_le_w n)
  have hnw : |(n : ℝ)| ≤ indexWeight n := abs_le_indexWeight n
  have hnR : ((⌈a⌉₊ + ⌈a + CI φ⌉₊ + 1 : ℕ) : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast hn
  push_cast at hnR
  have hc1 := Nat.le_ceil (a + CI φ)
  have hc0 : (0 : ℝ) ≤ (⌈a⌉₊ : ℝ) := Nat.cast_nonneg _
  have hwbig : a + CI φ ≤ indexWeight n := by linarith
  have ht : ‖t‖ ≤ 1 := by
    have e : t = (xi n - (n : ℂ) * (Real.pi : ℂ)) + Complex.I * ∑ k ∈ Finset.Icc 1 N,
        ((2 * Complex.I * xi n) ^ k)⁻¹ * integralRiccatiLeft φ k := by
      rw [htdef, wkbPhase_eq]; ring
    have h2 : 1 ≤ 2 * ‖xi n‖ := by linarith
    have hs := phase_sum_le φ (xi n) h2
    have hCI := CI_nonneg φ
    have h3 : CI φ / (2 * ‖xi n‖) ≤ CI φ / indexWeight n := div_le_div_of_nonneg_left hCI hw0 hwX
    have h4 : ‖t‖ ≤ a / indexWeight n + CI φ / indexWeight n := by
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add (hxi n) ?_)
      rw [norm_mul, Complex.norm_I, one_mul]
      exact hs.trans h3
    have h5 : a / indexWeight n + CI φ / indexWeight n = (a + CI φ) / indexWeight n := by ring
    rw [h5] at h4
    exact h4.trans ((div_le_one hw0).2 hwbig)
  have hcos : Complex.cos (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n)) =
      (-1 : ℂ) ^ n * Complex.cos t := by
    rw [← cos_int_mul_pi_add', htdef]; congr 1; ring
  have hsg : ‖(-1 : ℂ) ^ n‖ = 1 := by rw [norm_zpow, norm_neg, norm_one, one_zpow]
  have hct : ‖Complex.cos t - 1‖ ≤ 1 := (norm_cos_sub_one_le' ht).trans (by nlinarith [norm_nonneg t])
  have hr := hroot n
  set D := NlsGge.ThirdConsultation.KSPS.discriminant φ (xi n) with hDdef
  set s : ℂ := (-1 : ℂ) ^ n with hsdef
  have hdev : ‖D - 2 * s‖ ≤ 3 := by
    have e : D - 2 * s = (D - 2 * Complex.cos (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))) +
        2 * s * (Complex.cos t - 1) := by rw [hcos]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_ofNat, hsg]
    linarith
  have hss : s * s = 1 := by
    rcases sign_cases n with h | h <;> rw [hsdef, h] <;> norm_num
  have hfac : (D - 2 * s) * (D + 2 * s) = 0 := by
    linear_combination hr - 4 * hss
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have e : D - 2 * s = -(4 * s) := by linear_combination h
    rw [e, norm_neg, norm_mul, hsg, Complex.norm_ofNat] at hdev
    norm_num at hdev

/-! ### The quadratic identity -/

theorem quad_alg (s η α β ef et ε rf0 rf1 rt0 rt1 r00 r01 r10 r11 m00 m01 m10 m11 : ℂ)
    (hs : s = 1 ∨ s = -1) (hη : η ≠ 0) (hD : 1 - β * α ≠ 0)
    (hef : ef = s * η⁻¹) (het : et = s * η)
    (h00 : m00 = (1 - β * α)⁻¹ * (ef - α * β * et + ε * (rf0 - α * rt0)))
    (h01 : m01 = (1 - β * α)⁻¹ * (β * (et - ef) + ε * (rt0 - β * rf0)))
    (h10 : m10 = (1 - β * α)⁻¹ * (α * (ef - et) + ε * (rf1 - α * rt1)))
    (h11 : m11 = (1 - β * α)⁻¹ * (et - α * β * ef + ε * (rt1 - β * rf1)))
    (hr00 : r00 = s * ε * rf0) (hr01 : r01 = s * ε * rt0)
    (hr10 : r10 = s * ε * rf1) (hr11 : r11 = s * ε * rt1)
    (hdet : m00 * m11 - m01 * m10 = 1) (htr : m00 + m11 = 2 * s) :
    (-1 + α * β + r00 - β * r10) * η ^ 2 +
      (1 + (1 - r00) * (1 - r11) - α * β - (α - r10) * (β - r01)) * η +
      (-1 + α * β + r11 - α * r01) = 0 := by
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hzero : (s * m00 - 1) * (s * m11 - 1) - (s * m01) * (s * m10) = 0 := by
    linear_combination (s * s) * hdet - s * htr - hss
  have key : η * (1 - β * α) * ((s * m00 - 1) * (s * m11 - 1) - (s * m01) * (s * m10)) =
      (-1 + α * β + r00 - β * r10) * η ^ 2 +
        (1 + (1 - r00) * (1 - r11) - α * β - (α - r10) * (β - r01)) * η +
        (-1 + α * β + r11 - α * r01) := by
    subst h00 h01 h10 h11 hr00 hr01 hr10 hr11 hef het
    rcases hs with rfl | rfl <;> · field_simp; ring
  rw [← key, hzero, mul_zero]

/-! ### The concrete endpoint quadratic -/

theorem quad_zero_at {N : ℕ} (φ : SobolevC N) (n : ℤ) (lam : {z : ℂ // z ≠ 0})
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (hM : monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam)
    (hD : 1 - KSPSWKB.beta φ lam.1 0 * KSPSWKB.alpha φ lam.1 0 ≠ 0)
    (hsign : NlsGge.ThirdConsultation.KSPS.discriminant φ lam.1 = 2 * (-1 : ℂ) ^ n) :
    KSPSWKB.endpointQuadraticABC N φ n lam 0 *
        ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ lam.1)) ^ 2 +
      KSPSWKB.endpointQuadraticABC N φ n lam 1 *
        ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ lam.1)) +
      KSPSWKB.endpointQuadraticABC N φ n lam 2 = 0 := by
  set θ := NlsGge.ThirdConsultation.KSPS.wkbPhase φ lam.1 with hθ
  set s : ℂ := (-1 : ℂ) ^ n with hsdef
  set η : ℂ := s * Complex.exp (Complex.I * θ) with hηdef
  have hs : s = 1 ∨ s = -1 := sign_cases n
  have hex : Complex.exp (Complex.I * θ) ≠ 0 := Complex.exp_ne_zero _
  have hs0 : s ≠ 0 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hη : η ≠ 0 := mul_ne_zero hs0 hex
  have hef : ef φ lam = s * η⁻¹ := by
    rw [ef_eq, ← hθ, hηdef, mul_comm θ Complex.I, Complex.exp_neg]
    rcases hs with h | h <;> rw [h] <;> simp
  have het : et φ lam = s * η := by
    rw [et_eq φ lam h13, ← hθ, hηdef, mul_comm θ Complex.I]
    rcases hs with h | h <;> rw [h] <;> simp
  have hE := explicit_formula φ lam
  have hm : ∀ i j : Fin 2, monodromyPair (toPotPair φ) lam.1 i j = KSPSWKB.explicitWKBMonodromy N φ lam i j :=
    fun i j => by rw [hM]
  have hdet0 := det_monodromyPair (toPotPair φ) lam.1
  rw [Matrix.det_fin_two, hm 0 0, hm 0 1, hm 1 0, hm 1 1] at hdet0
  have htr0 : monodromyPair (toPotPair φ) lam.1 0 0 + monodromyPair (toPotPair φ) lam.1 1 1 = 2 * s := by
    rw [← discrim_eq]; exact hsign
  rw [hm 0 0, hm 1 1] at htr0
  have entry : ∀ i j : Fin 2, KSPSWKB.explicitWKBMonodromy N φ lam i j =
      ((1 - KSPSWKB.beta φ lam.1 0 * KSPSWKB.alpha φ lam.1 0)⁻¹ •
        !![ef φ lam - KSPSWKB.alpha φ lam.1 0 * KSPSWKB.beta φ lam.1 0 * et φ lam +
              ((2 * Complex.I * lam.1) ^ N)⁻¹ * (rf φ lam 0 - KSPSWKB.alpha φ lam.1 0 * rt φ lam 0),
           KSPSWKB.beta φ lam.1 0 * (et φ lam - ef φ lam) +
              ((2 * Complex.I * lam.1) ^ N)⁻¹ * (rt φ lam 0 - KSPSWKB.beta φ lam.1 0 * rf φ lam 0);
           KSPSWKB.alpha φ lam.1 0 * (ef φ lam - et φ lam) +
              ((2 * Complex.I * lam.1) ^ N)⁻¹ * (rf φ lam 1 - KSPSWKB.alpha φ lam.1 0 * rt φ lam 1),
           et φ lam - KSPSWKB.alpha φ lam.1 0 * KSPSWKB.beta φ lam.1 0 * ef φ lam +
              ((2 * Complex.I * lam.1) ^ N)⁻¹ * (rt φ lam 1 - KSPSWKB.beta φ lam.1 0 * rf φ lam 1)]) i j :=
    fun i j => by rw [hE]
  have hr : ∀ i j : Fin 2, KSPSWKB.scaledEndpointCorrection N φ n lam i j =
      s * ((2 * Complex.I * lam.1) ^ N)⁻¹ * (if j = 0 then rf φ lam i else rt φ lam i) :=
    fun i j => sec_apply φ n lam i j
  have hr00 := hr 0 0
  have hr01 := hr 0 1
  have hr10 := hr 1 0
  have hr11 := hr 1 1
  simp only [if_pos rfl, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, one_ne_zero, if_false] at hr00 hr01 hr10 hr11
  have e00 := entry 0 0
  have e01 := entry 0 1
  have e10 := entry 1 0
  have e11 := entry 1 1
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
    at e00 e01 e10 e11
  show (-1 + KSPSWKB.alpha φ lam.1 0 * KSPSWKB.beta φ lam.1 0 + KSPSWKB.scaledEndpointCorrection N φ n lam 0 0 -
        KSPSWKB.beta φ lam.1 0 * KSPSWKB.scaledEndpointCorrection N φ n lam 1 0) * η ^ 2 +
      (1 + (1 - KSPSWKB.scaledEndpointCorrection N φ n lam 0 0) *
          (1 - KSPSWKB.scaledEndpointCorrection N φ n lam 1 1) - KSPSWKB.alpha φ lam.1 0 * KSPSWKB.beta φ lam.1 0 -
        (KSPSWKB.alpha φ lam.1 0 - KSPSWKB.scaledEndpointCorrection N φ n lam 1 0) *
          (KSPSWKB.beta φ lam.1 0 - KSPSWKB.scaledEndpointCorrection N φ n lam 0 1)) * η +
      (-1 + KSPSWKB.alpha φ lam.1 0 * KSPSWKB.beta φ lam.1 0 + KSPSWKB.scaledEndpointCorrection N φ n lam 1 1 -
        KSPSWKB.alpha φ lam.1 0 * KSPSWKB.scaledEndpointCorrection N φ n lam 0 1) = 0
  exact quad_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs hη hD hef het e00 e01 e10 e11
    hr00 hr01 hr10 hr11 hdet0 htr0

end
end NlsGge.ThirdConsultation.KSPS026W
