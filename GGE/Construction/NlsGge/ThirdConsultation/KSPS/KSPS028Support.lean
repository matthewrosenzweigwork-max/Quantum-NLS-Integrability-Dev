import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS028Support4
import NlsGge.ThirdConsultation.KSPS.KSPS028Support3

                                                                                                                         
                                                                                                            
                                                                                                                     
                                                                                                                   
                                                                                                              
                                                                       
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS028W
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS021W NlsGge.ThirdConsultation.KSPS023W
open NlsGge.ThirdConsultation.KSPS024W NlsGge.ThirdConsultation.KSPS025W NlsGge.ThirdConsultation.KSPS027W

theorem Cb_nonneg (N : ℕ) (φ : SobolevC N) (CT : ℝ) (hCT : 0 ≤ CT) (n : ℤ) : 0 ≤ Cb N φ CT n := by
  have t0 := tP_nonneg N φ n
  have S0 := KSPS016W.Sb_nonneg φ
  have hL0 : 0 ≤ Lsum φ := Finset.sum_nonneg (fun k _ => by positivity)
  have hw0 : 0 ≤ indexWeight n := le_trans zero_le_one (KSPS015W.one_le_w n)
  unfold Cb Db
  have a1 : 0 ≤ (216 + 4 * KSPS016W.Sb φ) * tP N φ n := mul_nonneg (by linarith) t0
  have a2 : 0 ≤ indexWeight n ^ (N + 1) *
      ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n‖ :=
    mul_nonneg (pow_nonneg hw0 _) (norm_nonneg _)
  have a3 : 0 ≤ CT * 2 ^ (N + 2) * (1 / indexWeight n) :=
    mul_nonneg (mul_nonneg hCT (by positivity)) (div_nonneg zero_le_one hw0)
  have a4 : 0 ≤ 80 * Lsum φ * tP N φ n := mul_nonneg (mul_nonneg (by norm_num) hL0) t0
  linarith

theorem real_periodic_endpoint_expansion_of
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N)
    (h20 : ∀ B : ℝ, 0 < B →
      ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
        ∀ n : ℤ, N ≤ n.natAbs →
          max ‖periodicPlus φ n-(n:ℂ)*Real.pi‖
              ‖periodicMinus φ n-(n:ℂ)*Real.pi‖ ≤
            C/(n.natAbs:ℝ))
    (h26 : EndpointQuadraticWKB N φ)
    (h25 : WeightedL2Error (N+1)
      (fun n => NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n))
    (hre : ∀ n : ℤ, ∃ U L : ℝ, L ≤ U ∧ periodicPlus φ n = (U : ℂ) ∧ periodicMinus φ n = (L : ℂ))
    (hst : ∀ n : ℤ, physicalFourier (toPotPair φ).2 n = star (physicalFourier (toPotPair φ).1 (-n))) :
    ∃ eplus eminus : ℤ → ℂ,
      LpSequence 4 eplus ∧ LpSequence 4 eminus ∧
      ∀ n : ℤ, n ≠ 0 →
        periodicPlus φ n =
          spectralPolynomial φ n +
            ‖physicalFourier (toPotPair φ).1 (-n)‖ +
            eplus n / indexValue n^(N+1) ∧
        periodicMinus φ n =
          spectralPolynomial φ n -
            ‖physicalFourier (toPotPair φ).1 (-n)‖ +
            eminus n / indexValue n^(N+1) := by
  obtain ⟨a, ha, hloc⟩ := NlsGge.ThirdConsultation.KSPS026W.periodic_localization_of hN φ h20
  have hxp : ∀ m : ℤ, ‖periodicPlus φ m - (m : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight m := fun m => (hloc m).1
  have hxm : ∀ m : ℤ, ‖periodicMinus φ m - (m : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight m := fun m => (hloc m).2
  obtain ⟨hent, hplus, hminus, -, -, hevq⟩ := h26
  rw [Filter.cocompact_eq_cofinite] at hevq
  have htP := tP_sq_summable N φ hent
  have hs : ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hs, wl2_iff] at h25
  obtain ⟨ζ, hζa, hζ0, hev, hcoef⟩ :=
    NlsGge.ThirdConsultation.KSPS023T.spectralCoefficient_consistent φ (N + 1) le_rfl
  obtain ⟨CT0, hCT0⟩ := (hζa.hasFPowerSeriesAt.isBigO_sub_partialSum_pow (N + 2)).bound
  set CT : ℝ := max CT0 0 with hCTdef
  have hCT : 0 ≤ CT := le_max_right _ _
  have htay0 : ∀ᶠ y : ℂ in 𝓝 0, ‖ζ y - ∑ k ∈ Finset.Icc 1 (N + 1),
      KSPSRiccati.spectralCoefficient φ k * y ^ k‖ ≤ CT * ‖y‖ ^ (N + 2) := by
    filter_upwards [hCT0] with y hy
    rw [zero_add, partialSum_eq φ ζ hζ0 hcoef y, norm_pow, norm_norm] at hy
    exact hy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hsmall0 : ∀ᶠ y : ℂ in 𝓝 0, ‖ζ y‖ ≤ 1 := by
    have h := hζa.continuousAt.eventually (Metric.closedBall_mem_nhds (ζ 0) one_pos)
    filter_upwards [h] with y hy
    rw [dist_eq_norm, hζ0, sub_zero] at hy
    exact hy
  have et := tendsto_inv_int.eventually htay0
  have es := tendsto_inv_int.eventually hsmall0
  have ee := tendsto_inv_int.eventually hev
  have hDb : Summable (fun n : ℤ => Db N φ CT n ^ 2) := by
    have h := KSPS015W.sq_summable_add (KSPS015W.sq_summable_add
      (KSPS015W.sq_summable_mul_left (3 / 2) h25)
      (KSPS015W.sq_summable_mul_left (3 / 2)
        (KSPS015W.sq_summable_mul_left (CT * 2 ^ (N + 2)) KSPS016W.sq_summable_inv_w)))
      (KSPS015W.sq_summable_mul_left (80 * Lsum φ) htP)
    refine h.congr (fun n => ?_)
    unfold Db
    ring
  have hCb : Summable (fun n : ℤ => Cb N φ CT n ^ 2) := by
    have h := KSPS015W.sq_summable_add
      (KSPS015W.sq_summable_mul_left (216 + 4 * KSPS016W.Sb φ) htP)
      (KSPS015W.sq_summable_mul_left 2 hDb)
    refine h.congr (fun n => ?_)
    unfold Cb
    ring
  -- the tail estimate
  have e1 := KSPS015W.eventually_natAbs
    (⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1)
  have e2 := KSPS015W.eventually_natAbs (⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1)
  have e3 := KSPS015W.eventually_natAbs 1
  have e4 := eventually_w_ge (2 * (a + Jsum φ))
  have e5 := eventually_le_of_sq (tP N φ) htP (1 / 4) (by norm_num)
  have e6 := KSPS015W.eventually_natAbs ⌈2 * Lp φ⌉₊
  have e7 := KSPS015W.eventually_natAbs ⌈2 * Lsum φ⌉₊
  have hsq : ∀ n : ℤ, (1 : ℤ) ≤ |n| → ∀ M : ℝ, ((⌈M⌉₊ : ℤ) ≤ |n|) → M ≤ |(n : ℝ)| ^ 2 := by
    intro n g3 M g6
    have h7 : ((⌈M⌉₊ : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast g6
    rw [Int.cast_abs] at h7
    push_cast at h7
    have h8 := Nat.le_ceil M
    have h9 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast g3
      rw [Int.cast_abs] at this
      simpa using this
    nlinarith
  have hev28 : ∀ᶠ n : ℤ in cofinite,
      indexWeight n ^ (N + 1) * ‖periodicPlus φ n - spectralPolynomial φ n -
        (‖physicalFourier (toPotPair φ).1 (-n)‖ : ℂ)‖ ≤
        NlsGge.ThirdConsultation.KSPS028C.Qc N φ (KSPS016W.Sb φ) (tP N φ n) (Cb N φ CT n) n ∧
      indexWeight n ^ (N + 1) * ‖periodicMinus φ n - spectralPolynomial φ n +
        (‖physicalFourier (toPotPair φ).1 (-n)‖ : ℂ)‖ ≤
        NlsGge.ThirdConsultation.KSPS028C.Qc N φ (KSPS016W.Sb φ) (tP N φ n) (Cb N φ CT n) n := by
    filter_upwards [e1, e2, e3, e4, e5, e6, e7, et, es, ee, hevq] with
      n g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
    have hL := hsq n (by exact_mod_cast g3) _ g6
    have hL' := hsq n (by exact_mod_cast g3) _ g7
    obtain ⟨B, hB, hH⟩ := radicand_core N hN φ a ha hxp hxm hplus hminus ζ CT hCT n g1 g2 g4 g5 hL hL'
      g10.1 g10.2 g9 g8 g11
    obtain ⟨hp, hm, hqp, -⟩ := g11
    obtain ⟨-, hqp2, hqp3⟩ := hqp
    obtain ⟨R, -, -, hRw, hEw, hR, hα, hβ, -, -, -, -, -⟩ :=
      side_core N hN φ a ha true (periodicPlus φ) (fun _ => rfl) hxp n g1 g2 g4 g5 hp hqp2
    obtain ⟨-, -, hwX⟩ := KSPS015W.tail_facts a _ ha (periodicPlus φ) hxp n g1
    exact NlsGge.ThirdConsultation.KSPS028C.tail028_core N hN φ n hp (hplus n) B R (KSPS016W.Sb φ)
      (tP N φ n) (Cb N φ CT n) (KSPS016W.Sb_nonneg φ) (tP_nonneg N φ n) g5 (Cb_nonneg N φ CT hCT n)
      (KSPS015W.one_le_w n) hwX hqp3 hR hRw hEw hα hβ hB hH (hre n) (hst n)
  -- the explicit error sequences
  have hiv : ∀ n : ℤ, ((indexValue n : ℝ) : ℂ) ≠ 0 := by
    intro n h0
    have : indexValue n = 0 := by exact_mod_cast h0
    have h1 := KSPS015W.one_le_w n
    have h2 : indexValue n = indexWeight n := rfl
    linarith
  have hivn : ∀ n : ℤ, ‖((indexValue n : ℝ) : ℂ) ^ (N + 1)‖ = indexWeight n ^ (N + 1) := by
    intro n
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ indexValue n from le_trans zero_le_one (KSPS015W.one_le_w n))]
    rfl
  have hM : 0 ≤ NlsGge.ThirdConsultation.KSPS028C.Mc φ (KSPS016W.Sb φ) := by
    have S0 := KSPS016W.Sb_nonneg φ
    have i0 := norm_nonneg (integralRiccatiLeft φ (N + 1))
    have m1 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) i0) S0
    have m2 := sq_nonneg (1 + KSPS016W.Sb φ)
    have m3 := sq_nonneg (KSPS016W.Sb φ)
    unfold NlsGge.ThirdConsultation.KSPS028C.Mc
    linarith
  have hA0 : ∀ n : ℤ, 0 ≤ indexWeight n ^ (N + 1) *
      ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n‖ := fun n =>
    mul_nonneg (pow_nonneg (le_trans zero_le_one (KSPS015W.one_le_w n)) _) (norm_nonneg _)
  refine ⟨fun n => (periodicPlus φ n - spectralPolynomial φ n -
      (‖physicalFourier (toPotPair φ).1 (-n)‖ : ℂ)) * ((indexValue n : ℝ) : ℂ) ^ (N + 1),
    fun n => (periodicMinus φ n - spectralPolynomial φ n +
      (‖physicalFourier (toPotPair φ).1 (-n)‖ : ℂ)) * ((indexValue n : ℝ) : ℂ) ^ (N + 1), ?_, ?_, ?_⟩
  · refine NlsGge.ThirdConsultation.KSPS028C.lp4_of _ (tP N φ) (Cb N φ CT) _ hM _ h25 htP hCb hA0
      (tP_nonneg N φ) (Cb_nonneg N φ CT hCT) ?_
    filter_upwards [hev28] with n hn
    rw [norm_mul, hivn]
    exact (mul_comm _ _).le.trans hn.1
  · refine NlsGge.ThirdConsultation.KSPS028C.lp4_of _ (tP N φ) (Cb N φ CT) _ hM _ h25 htP hCb hA0
      (tP_nonneg N φ) (Cb_nonneg N φ CT hCT) ?_
    filter_upwards [hev28] with n hn
    rw [norm_mul, hivn]
    exact (mul_comm _ _).le.trans hn.2
  · intro n _
    have hc := pow_ne_zero (N + 1) (hiv n)
    push_cast
    constructor
    · rw [mul_div_assoc, div_self hc, mul_one]; ring
    · rw [mul_div_assoc, div_self hc, mul_one]; ring

end
end NlsGge.ThirdConsultation.KSPS028W
