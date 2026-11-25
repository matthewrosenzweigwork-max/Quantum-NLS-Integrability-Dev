import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS027Support

/- KSPS-028 SUPPORT4 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS028Support4.lean.
   radicand_core: the landed KSPS027W.tail027 argument copied VERBATIM up to (and including) its radicand relation hH
   and the bound hB, with the conclusion `∃ B, w^(N+1)|B| <= Cb ∧ 4((gamma/2)^2 - P) = -h+ + B^2 - 2 i gamma B`
   instead of tail027's final norm estimate (tail027 does not export the relation). No new mathematics. -/
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS028W
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS021W NlsGge.ThirdConsultation.KSPS023W
open NlsGge.ThirdConsultation.KSPS024W NlsGge.ThirdConsultation.KSPS025W NlsGge.ThirdConsultation.KSPS027W

theorem radicand_core (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxp : ∀ n : ℤ, ‖periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hxm : ∀ n : ℤ, ‖periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hplus hminus : ℤ → ℂ) (ζ : ℂ → ℂ) (CT : ℝ) (hCT : 0 ≤ CT) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tP N φ n ≤ 1 / 4)
    (hL : 2 * Lp φ ≤ |(n : ℝ)| ^ 2)
    (hL' : 2 * Lsum φ ≤ |(n : ℝ)| ^ 2)
    (hne : (Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹ ≠ 0)
    (heq : ζ (n : ℂ)⁻¹ + KSPSRiccati.phasePolynomial φ (N + 1)
      ((n : ℂ)⁻¹ / ((Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹)) = 0)
    (hsmall : ‖ζ (n : ℂ)⁻¹‖ ≤ 1)
    (htay : ‖ζ (n : ℂ)⁻¹ - ∑ k ∈ Finset.Icc 1 (N + 1),
        KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k‖ ≤ CT * ‖(n : ℂ)⁻¹‖ ^ (N + 2))
    (hqf : KSPSWKB.endpointQuadraticFormula N φ n hplus hminus) :
    ∃ B : ℂ, indexWeight n ^ (N + 1) * ‖B‖ ≤ Cb N φ CT n ∧
      4 * (((periodicPlus φ n - periodicMinus φ n) / 2) ^ 2 -
        physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n) =
      -hplus n + B ^ 2 - 2 * Complex.I * (periodicPlus φ n - periodicMinus φ n) * B := by
  have hg := gap_bound N hN φ a ha hxp hxm hplus hminus n h1 h2 h4 h5 hL hqf
  obtain ⟨hp, hm, hqp, -⟩ := hqf
  obtain ⟨-, hqp2, hqp3⟩ := hqp
  have hZ := side_Z N hN φ a ha true (periodicPlus φ) (fun _ => rfl) hxp n h1 h2 h4 h5 hp hqp2
  set Z : ℂ := 2 * KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 0 *
      ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (periodicPlus φ n))) +
      KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 1 with hZdef
  have hZsq : Z ^ 2 = -4 * physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n +
      hplus n := (Z_sq _ _ _ _ hqp2).trans hqp3
  -- basic facts
  obtain ⟨hn1R, hνa⟩ := KSPS016W.tail_nat a _ n h1
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  have hν0 : 0 < |(n : ℝ)| := by linarith
  have hwν : indexWeight n ≤ 2 * |(n : ℝ)| := KSPS015W.w_le_two n hn1R
  have htP0 := tP_nonneg N φ n
  have hnC : (n : ℂ) ≠ 0 := by
    intro h0
    have : (n : ℝ) = 0 := by exact_mod_cast h0
    rw [this, abs_zero] at hn1R
    linarith
  -- the exact germ solution
  set ls : ℂ := (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ with hls
  have hgs := lamStar_eq φ ζ n hnC hne heq
  rw [← hls] at hgs
  have hnpi : ‖(n : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; ring
  have hpi := Real.pi_gt_three
  have h10 : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hpi.le (abs_nonneg _)
  have hpν : |(n : ℝ)| ≤ ‖periodicPlus φ n‖ := by
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) (periodicPlus φ n)
    rw [norm_sub_rev, hnpi] at h7
    have h8 : a / indexWeight n ≤ a := div_le_self ha hw1
    have h9 := hxp n
    linarith
  have hlsν : |(n : ℝ)| ≤ ‖ls‖ := by
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) ls
    rw [norm_sub_rev, hnpi] at h7
    have h8 : ls - (n : ℂ) * (Real.pi : ℂ) = ζ (n : ℂ)⁻¹ := by rw [hls]; ring
    rw [h8] at h7
    linarith
  have hp0 : periodicPlus φ n ≠ 0 := hp
  have hls0 : ls ≠ 0 := by intro h0; rw [h0, norm_zero] at hlsν; linarith
  have hpi1 : ‖(periodicPlus φ n)⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hlsi : ‖ls⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hinv : ‖(periodicPlus φ n)⁻¹ - ls⁻¹‖ ≤ ‖periodicPlus φ n - ls‖ / |(n : ℝ)| ^ 2 := by
    rw [inv_sub_inv hp0 hls0, norm_div, norm_mul, norm_sub_rev]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hν0 2)
    rw [pow_two]
    exact mul_le_mul hpν hlsν hν0.le (norm_nonneg _)
  have hL0 : 0 ≤ Lsum φ := Finset.sum_nonneg (fun k _ => by positivity)
  have hΔp : ‖KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ -
      KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹‖ ≤ Lsum φ * ‖periodicPlus φ n - ls‖ / |(n : ℝ)| ^ 2 := by
    refine (phasePoly_lip φ (N + 1) _ _ hpi1 hlsi).trans ?_
    unfold Lsum
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hinv (Finset.sum_nonneg (fun k _ => by positivity))
  -- D := g(lam+) - n pi - gamma/2 = (tau - ls) + (P(1/lam+) - P(1/ls))
  set γ : ℂ := periodicPlus φ n - periodicMinus φ n with hγdef
  set τ : ℂ := NlsGge.ThirdConsultation.KSPS.midpoint φ n with hτdef
  have hτp : periodicPlus φ n = τ + γ / 2 := by
    rw [hτdef, hγdef]; unfold NlsGge.ThirdConsultation.KSPS.midpoint; ring
  set D : ℂ := periodicPlus φ n + KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ -
      (n : ℂ) * (Real.pi : ℂ) - γ / 2 with hDdef
  have hDe : D = (τ - ls) + (KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ -
      KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹) := by
    rw [hDdef]
    have := hτp
    linear_combination this + hgs
  have hT0 : ‖ls - spectralPolynomial φ n‖ ≤ CT * (1 / |(n : ℝ)| ^ (N + 2)) := by
    rw [spoly_eq, hls]
    have e : (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ - ((n : ℂ) * (Real.pi : ℂ) +
        ∑ k ∈ Finset.Icc 1 (N + 1), KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k) =
        ζ (n : ℂ)⁻¹ - ∑ k ∈ Finset.Icc 1 (N + 1),
          KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k := by ring
    rw [e]
    refine htay.trans (le_of_eq ?_)
    rw [norm_inv, Complex.norm_intCast, inv_pow]
    ring
  have hτls : ‖τ - ls‖ ≤ ‖τ - spectralPolynomial φ n‖ + CT * (1 / |(n : ℝ)| ^ (N + 2)) := by
    have e : τ - ls = (τ - spectralPolynomial φ n) - (ls - spectralPolynomial φ n) := by ring
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith)
  have hpls : ‖periodicPlus φ n - ls‖ ≤ ‖τ - ls‖ + ‖γ‖ / 2 := by
    rw [hτp]
    have e : τ + γ / 2 - ls = (τ - ls) + γ / 2 := by ring
    rw [e]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_div, Complex.norm_ofNat]
  have hLn : Lsum φ / |(n : ℝ)| ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (pow_pos hν0 2)]; linarith
  have hDn : ‖D‖ ≤ 3 / 2 * ‖τ - ls‖ + Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2) := by
    rw [hDe]
    refine (norm_add_le _ _).trans ?_
    have h7 : Lsum φ * ‖periodicPlus φ n - ls‖ / |(n : ℝ)| ^ 2 ≤
        Lsum φ / |(n : ℝ)| ^ 2 * ‖τ - ls‖ + Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2) := by
      have e1 : Lsum φ * ‖periodicPlus φ n - ls‖ / |(n : ℝ)| ^ 2 =
          Lsum φ / |(n : ℝ)| ^ 2 * ‖periodicPlus φ n - ls‖ := by ring
      have e2 : Lsum φ / |(n : ℝ)| ^ 2 * (‖τ - ls‖ + ‖γ‖ / 2) =
          Lsum φ / |(n : ℝ)| ^ 2 * ‖τ - ls‖ + Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2) := by
        ring
      rw [e1, ← e2]
      exact mul_le_mul_of_nonneg_left hpls (by positivity)
    have h8 : Lsum φ / |(n : ℝ)| ^ 2 * ‖τ - ls‖ ≤ 1 / 2 * ‖τ - ls‖ :=
      mul_le_mul_of_nonneg_right hLn (norm_nonneg _)
    linarith
  -- weighted D
  have hwp : 0 ≤ indexWeight n ^ (N + 1) := pow_nonneg hw0.le _
  have hD : indexWeight n ^ (N + 1) * ‖D‖ ≤ Db N φ CT n := by
    have hr := wpow_ratio N (indexWeight n) |(n : ℝ)| hw1 hn1R hwν
    have hγw : indexWeight n ^ (N + 1) * (Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2)) ≤ 80 * Lsum φ * tP N φ n := by
      have hwn2 : indexWeight n ^ 2 ≤ 4 * |(n : ℝ)| ^ 2 :=
        calc indexWeight n ^ 2 ≤ (2 * |(n : ℝ)|) ^ 2 := pow_le_pow_left₀ hw0.le hwν 2
          _ = 4 * |(n : ℝ)| ^ 2 := by ring
      have e : indexWeight n ^ (N + 1) * (Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2)) =
          Lsum φ / 2 * (indexWeight n ^ N * ‖γ‖) * (indexWeight n / |(n : ℝ)| ^ 2) := by
        ring
      have h7 : indexWeight n / |(n : ℝ)| ^ 2 ≤ 4 := by
        rw [div_le_iff₀ (pow_pos hν0 2)]
        have := le_self_pow₀ hw1 (by norm_num : (2 : ℕ) ≠ 0)
        linarith
      rw [e]
      have h8 : 0 ≤ Lsum φ / 2 * (indexWeight n ^ N * ‖γ‖) :=
        mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hw0.le _) (norm_nonneg _))
      calc Lsum φ / 2 * (indexWeight n ^ N * ‖γ‖) * (indexWeight n / |(n : ℝ)| ^ 2)
          ≤ Lsum φ / 2 * (indexWeight n ^ N * ‖γ‖) * 4 := mul_le_mul_of_nonneg_left h7 h8
        _ ≤ Lsum φ / 2 * (40 * tP N φ n) * 4 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by linarith)) (by norm_num)
        _ = 80 * Lsum φ * tP N φ n := by ring
    have hDn' : ‖D‖ ≤ 3 / 2 * (‖τ - spectralPolynomial φ n‖ + CT * (1 / |(n : ℝ)| ^ (N + 2))) +
        Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2) := by
      have := mul_le_mul_of_nonneg_left hτls (by norm_num : (0 : ℝ) ≤ 3 / 2)
      linarith
    have h9 := mul_le_mul_of_nonneg_left hDn' hwp
    have h11 : indexWeight n ^ (N + 1) * (CT * (1 / |(n : ℝ)| ^ (N + 2))) ≤
        CT * 2 ^ (N + 2) * (1 / indexWeight n) := by
      have := mul_le_mul_of_nonneg_left hr hCT
      calc indexWeight n ^ (N + 1) * (CT * (1 / |(n : ℝ)| ^ (N + 2)))
          = CT * (indexWeight n ^ (N + 1) * (1 / |(n : ℝ)| ^ (N + 2))) := by ring
        _ ≤ CT * (2 ^ (N + 2) * (1 / indexWeight n)) := this
        _ = CT * 2 ^ (N + 2) * (1 / indexWeight n) := by ring
    have e : indexWeight n ^ (N + 1) * (3 / 2 * (‖τ - spectralPolynomial φ n‖ +
        CT * (1 / |(n : ℝ)| ^ (N + 2))) + Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2)) =
        3 / 2 * (indexWeight n ^ (N + 1) * ‖τ - spectralPolynomial φ n‖) +
        3 / 2 * (indexWeight n ^ (N + 1) * (CT * (1 / |(n : ℝ)| ^ (N + 2)))) +
        indexWeight n ^ (N + 1) * (Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2)) := by ring
    unfold Db
    rw [← hτdef]
    linarith
  -- B' := Z + i gamma
  have hB : indexWeight n ^ (N + 1) * ‖Z + Complex.I * γ‖ ≤ Cb N φ CT n := by
    have e : Z + Complex.I * γ = (Z + 2 * Complex.I * (periodicPlus φ n +
        KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ - (n : ℂ) * (Real.pi : ℂ))) -
        2 * Complex.I * D := by rw [hDdef]; ring
    rw [e]
    have h7 := norm_sub_le (Z + 2 * Complex.I * (periodicPlus φ n +
        KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ - (n : ℂ) * (Real.pi : ℂ)))
      (2 * Complex.I * D)
    have h8 : ‖2 * Complex.I * D‖ = 2 * ‖D‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
    rw [h8] at h7
    have h9 := mul_le_mul_of_nonneg_left h7 hwp
    rw [mul_add] at h9
    unfold Cb
    linarith
  -- the radicand relation
  set B : ℂ := Z + Complex.I * γ with hBdef
  have hH : 4 * ((γ / 2) ^ 2 - physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n) =
      -hplus n + B ^ 2 - 2 * Complex.I * γ * B := by
    have hZB : Z = B - Complex.I * γ := by rw [hBdef]; ring
    rw [hZB] at hZsq
    linear_combination (-1 : ℂ) * hZsq + γ ^ 2 * Complex.I_sq
  exact ⟨B, hB, hH⟩

end
end NlsGge.ThirdConsultation.KSPS028W
