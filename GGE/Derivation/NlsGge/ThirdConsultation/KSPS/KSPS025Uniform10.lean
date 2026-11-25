import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS024Support

/- KSPS025U10 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS025Uniform10.lean. Pro round-15 SUPPORT (never a packet), chain B.
   h24 REDUCTION: the uniform KSPS-024 tail hypothesis h24 of KSPS025U7/U8 (finite weighted sums of
   criticalEigenvalue - spectralPolynomial over a uniform tail, one constant for the whole order-N ball) follows from
   the ball-uniform KSPS-017 tail at xi = criticalEigenvalue (hypothesis h17U, finite weighted sums of the
   discriminant-derivative error over a uniform tail), with everything else proved:
   - tail024A_U / tail024_U: the landed KSPS024W.tail024A / tail024 bodies (copied, only changes listed here) WITHOUT
     the smallness hypothesis tauC ≤ 1: the quadratic sine term is bounded by tauC² (sq_weight_le_U) instead of tauC,
     so psiCU = 4 Lp tauC + 4 tauC² + w^(N+1)‖critE‖/2 and boundCU = psiCU + Lsum (2 psiCU) + CT 2^(N+2)/w;
   - uniform constants: KSPSU1.crit_localization_uniform (a), KSPS025U5.riccati_consts_uniform (Jsum, Lp, Lsum,
     ‖I_(N+1)‖ ≤ L), KSPS025U9.germ_uniform (one radius r0, one Taylor constant CT, all φ);
   - one cutoff M (all of h17U's cutoff, the tail024 conditions and the germ radius), and finite-sum algebra:
     Σ tauC⁴ ≤ (Σ tauC²)², Σ (1/w)² ≤ its tsum.
   CORE/GLUE split (lane memory cap): this CORE theorem h24_of17_of takes the three proved uniform inputs as
   hypotheses hloc/hconst/hgerm of EXACTLY the types of KSPSU1.crit_localization_uniform,
   KSPS025U5.riccati_consts_uniform and KSPS025U9.germ_uniform; the GLUE KSPS025Uniform11 discharges them.
   h17U is a genuinely open ball-uniform KSPS-017 companion (see HANDOFF / KSPS025U10_STOP.md). -/
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS025U10
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS021W NlsGge.ThirdConsultation.KSPS023W
open NlsGge.ThirdConsultation.KSPS024W

def psiCU (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℝ :=
  4 * Lp φ * tauC N φ n + 4 * tauC N φ n ^ 2 + indexWeight n ^ (N + 1) * ‖critE N φ n‖ / 2

def boundCU (N : ℕ) (φ : SobolevC N) (CT : ℝ) (n : ℤ) : ℝ :=
  psiCU N φ n + Lsum φ * (2 * psiCU N φ n) + CT * 2 ^ (N + 2) * (1 / indexWeight n)

theorem sq_weight_le_U (N : ℕ) (hN : 1 ≤ N) (w s t : ℝ) (hw : 1 ≤ w) (hs : 0 ≤ s)
    (hst : w ^ N * s ≤ t) :
    w ^ (N + 1) * s ^ 2 ≤ t ^ 2 := by
  have hw0 : 0 ≤ w := by linarith
  have h0 : 0 ≤ w ^ N * s := mul_nonneg (pow_nonneg hw0 _) hs
  have h1 : w ^ (N + 1) ≤ w ^ (2 * N) := pow_le_pow_right₀ hw (by omega)
  have h2 : w ^ (N + 1) * s ^ 2 ≤ w ^ (2 * N) * s ^ 2 :=
    mul_le_mul_of_nonneg_right h1 (sq_nonneg s)
  have h3 : w ^ (2 * N) * s ^ 2 = (w ^ N * s) ^ 2 := by ring
  have h4 : (w ^ N * s) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ h0 hst 2
  linarith

theorem tail024A_U (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈2 * Lp φ + 1⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n) :
    ∃ r2 : ℂ, indexWeight n ^ (N + 1) * ‖r2‖ ≤ psiCU N φ n ∧
      criticalEigenvalue φ n +
        KSPSRiccati.phasePolynomial φ (N + 1) (criticalEigenvalue φ n)⁻¹ -
          (n : ℂ) * (Real.pi : ℂ) = r2 := by
  obtain ⟨hX1, hXT, hwX⟩ := KSPS015W.tail_facts a (2 * Lp φ + 1) ha (criticalEigenvalue φ) hxi n h1
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  have hLp0 := Lp_nonneg φ
  have hroot := deriv_discriminant_crit φ n
  set X : ℂ := criticalEigenvalue φ n with hXdef
  set θp : ℂ := KSPSWKB.phaseDerivative φ X with hθpdef
  set IL : ℂ := integralRiccatiLeft φ (N + 1) with hILdef
  set e : ℂ := critE N φ n with hedef
  -- theta' bounds
  have hθ1 := phaseDerivative_sub_one_le φ X hX1
  rw [← hθpdef] at hθ1
  have hX2 : ‖X‖ ≤ ‖X‖ ^ 2 := by nlinarith [hX1]
  have hθ2 : ‖θp - 1‖ ≤ 1 / 2 := by
    refine hθ1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hθl : 1 / 2 ≤ ‖θp‖ := by
    have h := norm_sub_le θp (θp - 1)
    rw [sub_sub_cancel, norm_one] at h
    linarith
  have hθ4 : ‖1 - θp‖ ≤ 4 * Lp φ / indexWeight n ^ 2 := by
    rw [norm_sub_rev]
    refine hθ1.trans ?_
    have hw2 : indexWeight n ^ 2 ≤ 4 * ‖X‖ ^ 2 := by nlinarith [hwX, hw0]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [mul_le_mul_of_nonneg_left hw2 hLp0]
  -- (1) the exact identity at the critical root
  obtain ⟨-, hsn⟩ := shift (NlsGge.ThirdConsultation.KSPS.wkbPhase φ X) n
  set θ : ℂ := NlsGge.ThirdConsultation.KSPS.wkbPhase φ X with hθ
  set ε : ℂ := θ - (n : ℂ) * (Real.pi : ℂ) with hεdef
  have hsg1 : (-1 : ℂ) ^ (n + 1) = -(-1 : ℂ) ^ n := by
    rw [zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]; ring
  have he : e = 0 - (-2 * ((-1 : ℂ) ^ n * Complex.sin ε) * θp +
      2 * Complex.I * (-(-1 : ℂ) ^ n) / (2 * Complex.I * X) ^ (N + 1) * IL) := by
    rw [hedef]
    unfold critE KSPSWKB.discriminantDerivativeMain
    rw [← hXdef, hroot, ← hθpdef, ← hθ, hsn, hsg1, ← hILdef]
  have hsi := crit_sine_identity (Complex.sin ε) θp e IL ((2 * Complex.I * X) ^ (N + 1))
    ((-1 : ℂ) ^ n) (neg_one_zpow_mul_self n) he
  have hpi := crit_product_identity (Complex.sin ε) θp e IL ((2 * Complex.I * X) ^ (N + 1))
    ((-1 : ℂ) ^ n) (neg_one_zpow_mul_self n) he
  -- the sine estimate
  have hY : ‖(2 * Complex.I * X) ^ (N + 1)‖ = (2 * ‖X‖) ^ (N + 1) := by
    rw [norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  have hX0 : 0 < ‖X‖ := by linarith
  have hYpos : 0 < (2 * ‖X‖) ^ (N + 1) := by positivity
  have hs : ‖Complex.sin ε‖ ≤ ‖e‖ + (0 + 0) + 2 * ‖IL‖ / (2 * ‖X‖) ^ (N + 1) := by
    have hr : ‖(-1 : ℂ) ^ n * e / 2 - Complex.I * IL / (2 * Complex.I * X) ^ (N + 1)‖ ≤
        ‖e‖ / 2 + ‖IL‖ / (2 * ‖X‖) ^ (N + 1) := by
      refine (norm_sub_le _ _).trans (le_of_eq ?_)
      rw [norm_div, norm_mul, norm_neg_one_zpow, one_mul, Complex.norm_ofNat, norm_div, norm_mul,
        Complex.norm_I, one_mul, hY]
    rw [← hpi, norm_mul] at hr
    have h6 : ‖Complex.sin ε‖ * (1 / 2) ≤ ‖Complex.sin ε‖ * ‖θp‖ :=
      mul_le_mul_of_nonneg_left hθl (norm_nonneg _)
    have h7 : 2 * ‖IL‖ / (2 * ‖X‖) ^ (N + 1) = 2 * (‖IL‖ / (2 * ‖X‖) ^ (N + 1)) := by ring
    rw [h7]
    linarith
  have hst : indexWeight n ^ N * ‖Complex.sin ε‖ ≤ tauC N φ n := by
    have h8 := tau_pure N (indexWeight n) ‖X‖ ‖e‖ 0 0 0 0 ‖IL‖ ‖Complex.sin ε‖ hw1 hwX (norm_nonneg _)
      (norm_nonneg _) (by simp) (by simp) hs
    unfold tauC
    rw [← hedef, ← hILdef]
    linarith
  -- eps is small
  have hε : ‖ε‖ ≤ 1 / 2 := by
    have := phase_small φ X n (indexWeight n) a hw0 hX1 hwX (hxi n)
    have h7 : (a + Jsum φ) / indexWeight n ≤ 1 / 2 := by
      rw [div_le_iff₀ hw0]
      linarith
    unfold Jsum at h7
    rw [hεdef, hθ]
    linarith
  have hεs := eps_le_two_sin ε hε
  have hss := norm_sin_sub_self_le ε (by linarith)
  -- (2) the remainder r2
  set r2 : ℂ := (ε - Complex.sin ε) + ((1 - θp) * Complex.sin ε + (-1 : ℂ) ^ n * e / 2) with hr2def
  have hr2 : indexWeight n ^ (N + 1) * ‖r2‖ ≤ psiCU N φ n := by
    have hb : ‖r2‖ ≤ 4 * ‖Complex.sin ε‖ ^ 2 +
        4 * Lp φ / indexWeight n ^ 2 * ‖Complex.sin ε‖ + ‖e‖ / 2 := by
      have e1 : ‖ε - Complex.sin ε‖ ≤ 4 * ‖Complex.sin ε‖ ^ 2 := by
        rw [norm_sub_rev]
        refine hss.trans ?_
        calc ‖ε‖ ^ 2 ≤ (2 * ‖Complex.sin ε‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hεs 2
          _ = 4 * ‖Complex.sin ε‖ ^ 2 := by ring
      have e2 : ‖(1 - θp) * Complex.sin ε‖ ≤ 4 * Lp φ / indexWeight n ^ 2 * ‖Complex.sin ε‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hθ4 (norm_nonneg _)
      have e3 : ‖(-1 : ℂ) ^ n * e / 2‖ = ‖e‖ / 2 := by
        rw [norm_div, norm_mul, norm_neg_one_zpow, one_mul, Complex.norm_ofNat]
      calc ‖r2‖ ≤ ‖ε - Complex.sin ε‖ +
            (‖(1 - θp) * Complex.sin ε‖ + ‖(-1 : ℂ) ^ n * e / 2‖) := by
            rw [hr2def]
            exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ _ := by rw [e3]; linarith
    have hsq := sq_weight_le_U N hN (indexWeight n) ‖Complex.sin ε‖ (tauC N φ n) hw1 (norm_nonneg _) hst
    have hlin : indexWeight n ^ (N + 1) * (4 * Lp φ / indexWeight n ^ 2 * ‖Complex.sin ε‖) ≤
        4 * Lp φ * tauC N φ n := by
      have e : indexWeight n ^ (N + 1) * (4 * Lp φ / indexWeight n ^ 2 * ‖Complex.sin ε‖) =
          4 * Lp φ * (indexWeight n ^ N * ‖Complex.sin ε‖) / indexWeight n := by
        rw [pow_succ]
        field_simp
      rw [e]
      have h0 : 0 ≤ 4 * Lp φ * (indexWeight n ^ N * ‖Complex.sin ε‖) :=
        mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hw0.le _) (norm_nonneg _))
      refine (div_le_self h0 hw1).trans ?_
      exact mul_le_mul_of_nonneg_left hst (by linarith)
    have hwp : 0 ≤ indexWeight n ^ (N + 1) := pow_nonneg hw0.le _
    have h6 := mul_le_mul_of_nonneg_left hb hwp
    have e : indexWeight n ^ (N + 1) * (4 * ‖Complex.sin ε‖ ^ 2 +
        4 * Lp φ / indexWeight n ^ 2 * ‖Complex.sin ε‖ + ‖e‖ / 2) =
        4 * (indexWeight n ^ (N + 1) * ‖Complex.sin ε‖ ^ 2) +
          indexWeight n ^ (N + 1) * (4 * Lp φ / indexWeight n ^ 2 * ‖Complex.sin ε‖) +
          indexWeight n ^ (N + 1) * ‖e‖ / 2 := by ring
    rw [e] at h6
    unfold psiCU
    rw [← hedef]
    linarith
  -- g(lamDot) - n pi = r2
  have hg : X + KSPSRiccati.phasePolynomial φ (N + 1) X⁻¹ - (n : ℂ) * (Real.pi : ℂ) = r2 := by
    rw [phase_poly_eq φ X, ← hθ, ← hILdef]
    have e : θ = ε + (n : ℂ) * (Real.pi : ℂ) := by rw [hεdef]; ring
    rw [e, hr2def]
    linear_combination hsi
  exact ⟨r2, hr2, hg⟩

theorem tail024_U (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (ζ : ℂ → ℂ) (CT : ℝ) (hCT : 0 ≤ CT) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈2 * Lp φ + 1⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (hL : 2 * Lsum φ ≤ |(n : ℝ)| ^ 2)
    (hne : (Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹ ≠ 0)
    (heq : ζ (n : ℂ)⁻¹ + KSPSRiccati.phasePolynomial φ (N + 1)
      ((n : ℂ)⁻¹ / ((Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹)) = 0)
    (hsmall : ‖ζ (n : ℂ)⁻¹‖ ≤ 1)
    (htay : ‖ζ (n : ℂ)⁻¹ - ∑ k ∈ Finset.Icc 1 (N + 1),
        KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k‖ ≤ CT * ‖(n : ℂ)⁻¹‖ ^ (N + 2)) :
    indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖ ≤
      boundCU N φ CT n := by
  obtain ⟨r2, hr2, hg⟩ := tail024A_U N hN φ a ha hxi n h1 h4
  obtain ⟨hν1, hνa⟩ := KSPS016W.tail_nat a _ n h1
  have hn1R : (1 : ℝ) ≤ |(n : ℝ)| := hν1
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  have hnC : (n : ℂ) ≠ 0 := by
    intro h0
    have : (n : ℝ) = 0 := by exact_mod_cast h0
    rw [this, abs_zero] at hn1R
    linarith
  set ls : ℂ := (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ with hls
  have hgs := lamStar_eq φ ζ n hnC hne heq
  rw [← hls] at hgs
  set X : ℂ := criticalEigenvalue φ n with hXdef
  have hnpi : ‖(n : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; ring
  have hpi := Real.pi_gt_three
  have hμν : |(n : ℝ)| ≤ ‖X‖ := by
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) X
    rw [norm_sub_rev, hnpi] at h7
    have h8 : a / indexWeight n ≤ a := div_le_self ha hw1
    have h9 := hxi n
    rw [← hXdef] at h9
    have h10 : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hpi.le (abs_nonneg _)
    linarith
  have hlsν : |(n : ℝ)| ≤ ‖ls‖ := by
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) ls
    rw [norm_sub_rev, hnpi] at h7
    have h8 : ls - (n : ℂ) * (Real.pi : ℂ) = ζ (n : ℂ)⁻¹ := by rw [hls]; ring
    rw [h8] at h7
    have h10 : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hpi.le (abs_nonneg _)
    linarith
  have hν0 : 0 < |(n : ℝ)| := by linarith
  have hμ0 : X ≠ 0 := by intro h0; rw [h0, norm_zero] at hμν; linarith
  have hls0 : ls ≠ 0 := by intro h0; rw [h0, norm_zero] at hlsν; linarith
  have hμi : ‖X⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hlsi : ‖ls⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hinv : ‖X⁻¹ - ls⁻¹‖ ≤ ‖X - ls‖ / |(n : ℝ)| ^ 2 := by
    rw [inv_sub_inv hμ0 hls0, norm_div, norm_mul, norm_sub_rev]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hν0 2)
    rw [pow_two]
    exact mul_le_mul hμν hlsν hν0.le (norm_nonneg _)
  have hlip := phasePoly_lip φ (N + 1) _ _ hμi hlsi
  have hΔp : ‖KSPSRiccati.phasePolynomial φ (N + 1) X⁻¹ -
      KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹‖ ≤ Lsum φ * ‖X - ls‖ / |(n : ℝ)| ^ 2 := by
    refine hlip.trans ?_
    unfold Lsum
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hinv (Finset.sum_nonneg (fun k _ => by positivity))
  have hDeq : (X - ls) + (KSPSRiccati.phasePolynomial φ (N + 1) X⁻¹ -
      KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹) = (0 : ℂ) / 2 + r2 := by
    rw [zero_div, zero_add, ← hg]
    linear_combination (-1 : ℂ) * hgs
  have hT0 : ‖ls - spectralPolynomial φ n‖ ≤ CT / |(n : ℝ)| ^ (N + 2) := by
    rw [spoly_eq, hls]
    have e : (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ - ((n : ℂ) * (Real.pi : ℂ) +
        ∑ k ∈ Finset.Icc 1 (N + 1), KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k) =
        ζ (n : ℂ)⁻¹ - ∑ k ∈ Finset.Icc 1 (N + 1),
          KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k := by ring
    rw [e]
    refine htay.trans (le_of_eq ?_)
    rw [norm_inv, Complex.norm_intCast, inv_pow]
    ring
  have hG : indexWeight n ^ N * ‖(0 : ℂ)‖ ≤ 0 := by simp
  have hwν : indexWeight n ≤ 2 * |(n : ℝ)| := KSPS015W.w_le_two n hn1R
  have hL0 : 0 ≤ Lsum φ := Finset.sum_nonneg (fun k _ => by positivity)
  have hfin := final_pure N (indexWeight n) |(n : ℝ)| (Lsum φ) CT 0
    (psiCU N φ n) (X - ls) 0 r2
    (KSPSRiccati.phasePolynomial φ (N + 1) X⁻¹ - KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹)
    (ls - spectralPolynomial φ n)
    hw1 hn1R hwν hL0 hL hCT hDeq hΔp hT0 hG hr2
  have e : X - spectralPolynomial φ n =
      r2 - (KSPSRiccati.phasePolynomial φ (N + 1) X⁻¹ -
        KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹) + (ls - spectralPolynomial φ n) := by
    linear_combination hDeq
  rw [e]
  have e2 : (4 : ℝ) * 0 + 2 * psiCU N φ n = 2 * psiCU N φ n := by ring
  rw [e2] at hfin
  unfold boundCU
  exact hfin

/-! ### Finite-sum algebra and the uniform assembly -/

theorem sq4_le (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

theorem sum_sq_le_sq_sum (F : Finset ℤ) (x : ℤ → ℝ) (h0 : ∀ n ∈ F, 0 ≤ x n) :
    ∑ n ∈ F, x n ^ 2 ≤ (∑ n ∈ F, x n) ^ 2 := by
  rw [sq (∑ n ∈ F, x n), Finset.sum_mul]
  refine Finset.sum_le_sum (fun n hn => ?_)
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum h0 hn) (h0 n hn)

theorem le_abs_of_ceil (x : ℝ) (n : ℤ) (h : ((⌈x⌉₊ : ℕ) : ℤ) ≤ |n|) : x ≤ |(n : ℝ)| := by
  have h1 : (((⌈x⌉₊ : ℕ) : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h
  rw [Int.cast_abs] at h1
  push_cast at h1
  exact (Nat.le_ceil x).trans h1

theorem abs_le_w (n : ℤ) : |(n : ℝ)| ≤ indexWeight n := by
  unfold indexWeight
  exact Real.abs_le_sqrt (by nlinarith)

/-- Pure finite-sum step. -/
theorem sum_part (F : Finset ℤ) (x E v : ℤ → ℝ) (L α β γ δ C S : ℝ)
    (hx0 : ∀ n ∈ F, 0 ≤ x n) (hE0 : ∀ n ∈ F, 0 ≤ E n) (hv0 : ∀ n ∈ F, 0 ≤ v n) (hL : 0 ≤ L)
    (hx : ∀ n ∈ F, x n ≤ α * (E n + 2 * L * v n) + β * (E n + 2 * L * v n) ^ 2 + γ * E n + δ * v n)
    (hE : ∑ n ∈ F, E n ^ 2 ≤ C) (hv : ∑ n ∈ F, v n ^ 2 ≤ S) :
    ∑ n ∈ F, x n ^ 2 ≤
      4 * (α ^ 2 * (2 * C + 8 * L ^ 2 * S) + β ^ 2 * (2 * C + 8 * L ^ 2 * S) ^ 2 + γ ^ 2 * C + δ ^ 2 * S) := by
  set T : ℝ := 2 * C + 8 * L ^ 2 * S with hT
  have hτsum : ∑ n ∈ F, (E n + 2 * L * v n) ^ 2 ≤ T := by
    have h1 : ∀ n ∈ F, (E n + 2 * L * v n) ^ 2 ≤ 2 * E n ^ 2 + 8 * L ^ 2 * v n ^ 2 := fun n _ => by
      nlinarith [sq_nonneg (E n - 2 * L * v n)]
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ 8 * L ^ 2)
    rw [hT]
    linarith
  have hτ4 : ∑ n ∈ F, ((E n + 2 * L * v n) ^ 2) ^ 2 ≤ T ^ 2 :=
    (sum_sq_le_sq_sum F (fun n => (E n + 2 * L * v n) ^ 2) (fun n _ => sq_nonneg _)).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun n _ => sq_nonneg _)) hτsum 2)
  have hkey : ∀ n ∈ F, x n ^ 2 ≤
      4 * α ^ 2 * (E n + 2 * L * v n) ^ 2 + 4 * β ^ 2 * ((E n + 2 * L * v n) ^ 2) ^ 2 +
        4 * γ ^ 2 * E n ^ 2 + 4 * δ ^ 2 * v n ^ 2 := by
    intro n hn
    refine (pow_le_pow_left₀ (hx0 n hn) (hx n hn) 2).trans ?_
    refine (sq4_le _ _ _ _).trans (le_of_eq ?_)
    ring
  refine (Finset.sum_le_sum hkey).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have a1 := mul_le_mul_of_nonneg_left hτsum (by positivity : (0 : ℝ) ≤ 4 * α ^ 2)
  have a2 := mul_le_mul_of_nonneg_left hτ4 (by positivity : (0 : ℝ) ≤ 4 * β ^ 2)
  have a3 := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ 4 * γ ^ 2)
  have a4 := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ 4 * δ ^ 2)
  linarith

/-- The per-index bound on a uniform tail. -/
theorem per_index (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (L : ℝ) (hL : 0 ≤ L) (hJ : Jsum φ ≤ L) (hLp : Lp φ ≤ L) (hLs : Lsum φ ≤ L)
    (hI : ‖integralRiccatiLeft φ (N + 1)‖ ≤ L) (r0 : ℝ) (hr0 : 0 < r0) (CT : ℝ) (hCT : 0 ≤ CT)
    (ζ : ℂ → ℂ) (hζ : ∀ y : ℂ, ‖y‖ ≤ r0 →
        (Real.pi : ℂ) + y * ζ y ≠ 0 ∧
        ζ y + NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ (N + 1)
          (y / ((Real.pi : ℂ) + y * ζ y)) = 0 ∧
        ‖ζ y‖ ≤ 1 ∧
        ‖ζ y - ∑ k ∈ Finset.Icc 1 (N + 1),
            NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ k * y ^ k‖ ≤
          CT * ‖y‖ ^ (N + 2))
    (n : ℤ) (hM : ((⌈a⌉₊ + ⌈2 * L + 1⌉₊ + 1 + ⌈2 * (a + L)⌉₊ + ⌈2 * L⌉₊ + ⌈1 / r0⌉₊ : ℕ) : ℤ) ≤ |n|) :
    indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖ ≤
      ((1 + 2 * L) * (4 * L)) * (indexWeight n ^ (N + 1) * ‖critE N φ n‖ + 2 * L * (1 / indexWeight n)) +
      ((1 + 2 * L) * 4) * (indexWeight n ^ (N + 1) * ‖critE N φ n‖ + 2 * L * (1 / indexWeight n)) ^ 2 +
      ((1 + 2 * L) / 2) * (indexWeight n ^ (N + 1) * ‖critE N φ n‖) +
      (CT * 2 ^ (N + 2)) * (1 / indexWeight n) := by
  have hw1 := KSPS015W.one_le_w n
  have hv0 : 0 ≤ 1 / indexWeight n := div_nonneg zero_le_one (by linarith)
  have hE0 : 0 ≤ indexWeight n ^ (N + 1) * ‖critE N φ n‖ :=
    mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _)
  have hM' := hM
  push_cast at hM'
  have g1 : ((⌈a⌉₊ + ⌈2 * Lp φ + 1⌉₊ + 1 : ℕ) : ℤ) ≤ |n| := by
    have : ⌈2 * Lp φ + 1⌉₊ ≤ ⌈2 * L + 1⌉₊ := Nat.ceil_mono (by linarith)
    push_cast
    omega
  have g4 : 2 * (a + Jsum φ) ≤ indexWeight n := by
    have h1 := le_abs_of_ceil (2 * (a + L)) n (by omega)
    linarith [abs_le_w n]
  have hab : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ |n| by omega)
    rw [Int.cast_abs] at this
    simpa using this
  have hLn : 2 * Lsum φ ≤ |(n : ℝ)| ^ 2 := by
    have h1 := le_abs_of_ceil (2 * L) n (by omega)
    nlinarith
  have hy : ‖((n : ℂ))⁻¹‖ ≤ r0 := by
    have h1 := le_abs_of_ceil (1 / r0) n (by omega)
    rw [norm_inv, Complex.norm_intCast]
    rw [one_div] at h1
    exact inv_le_of_inv_le₀ hr0 h1
  obtain ⟨hne, heq, hsmall, htay⟩ := hζ _ hy
  have ht := tail024_U N hN φ a ha hxi ζ CT hCT n g1 g4 hLn hne heq hsmall htay
  refine ht.trans ?_
  set E : ℝ := indexWeight n ^ (N + 1) * ‖critE N φ n‖ with hEdef
  set v : ℝ := 1 / indexWeight n with hvdef
  have htau : tauC N φ n ≤ E + 2 * L * v := by
    unfold tauC
    rw [← hEdef, ← hvdef]
    have := mul_le_mul_of_nonneg_right hI hv0
    nlinarith
  have htau0 : 0 ≤ tauC N φ n := by
    unfold tauC
    rw [← hEdef, ← hvdef]
    have h3 : 0 ≤ 2 * ‖integralRiccatiLeft φ (N + 1)‖ * v := mul_nonneg (by positivity) hv0
    linarith
  have hpsi : psiCU N φ n ≤ 4 * L * (E + 2 * L * v) + 4 * (E + 2 * L * v) ^ 2 + E / 2 := by
    unfold psiCU
    rw [← hEdef]
    have h1 : 4 * Lp φ * tauC N φ n ≤ 4 * L * (E + 2 * L * v) := by
      have := mul_le_mul hLp htau htau0 hL
      nlinarith
    have h2 : tauC N φ n ^ 2 ≤ (E + 2 * L * v) ^ 2 := pow_le_pow_left₀ htau0 htau 2
    linarith
  have hpsi0 : 0 ≤ psiCU N φ n := by
    unfold psiCU
    rw [← hEdef]
    have h1 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Lp_nonneg φ)) htau0
    nlinarith [sq_nonneg (tauC N φ n)]
  unfold boundCU
  rw [← hvdef]
  have h3 : Lsum φ * (2 * psiCU N φ n) ≤
      L * (2 * (4 * L * (E + 2 * L * v) + 4 * (E + 2 * L * v) ^ 2 + E / 2)) :=
    mul_le_mul hLs (by linarith) (by linarith) hL
  have e : ((1 + 2 * L) * (4 * L)) * (E + 2 * L * v) + ((1 + 2 * L) * 4) * (E + 2 * L * v) ^ 2 +
      ((1 + 2 * L) / 2) * E + (CT * 2 ^ (N + 2)) * v =
      (4 * L * (E + 2 * L * v) + 4 * (E + 2 * L * v) ^ 2 + E / 2) +
        L * (2 * (4 * L * (E + 2 * L * v) + 4 * (E + 2 * L * v) ^ 2 + E / 2)) +
        CT * 2 ^ (N + 2) * v := by ring
  rw [e]
  linarith

/-- h24 from the ball-uniform KSPS-017 tail at the critical points (core; uniform inputs as hypotheses). -/
theorem h24_of17_of (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀)
    (hloc : ∃ a : ℝ, 0 ≤ a ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ n : ℤ, ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hconst : ∃ L : ℝ, 0 ≤ L ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      Jsum φ ≤ L ∧ NlsGge.ThirdConsultation.KSPS024W.Lp φ ≤ L ∧ NlsGge.ThirdConsultation.KSPS023W.Lsum φ ≤ L ∧
        ‖integralRiccatiLeft φ (N + 1)‖ ≤ L)
    (hgerm0 : ∃ r0 : ℝ, 0 < r0 ∧ ∃ CT : ℝ, 0 ≤ CT ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∃ ζ : ℂ → ℂ, ∀ y : ℂ, ‖y‖ ≤ r0 →
        (Real.pi : ℂ) + y * ζ y ≠ 0 ∧
        ζ y + NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ (N + 1)
          (y / ((Real.pi : ℂ) + y * ζ y)) = 0 ∧
        ‖ζ y‖ ≤ 1 ∧
        ‖ζ y - ∑ k ∈ Finset.Icc 1 (N + 1),
            NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ k * y ^ k‖ ≤
          CT * ‖y‖ ^ (N + 2))
    (h17U : ∃ (M : ℕ) (C : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) *
          ‖deriv (discriminant φ) (criticalEigenvalue φ n) -
            NlsGge.ThirdConsultation.KSPSWKB.discriminantDerivativeMain N φ (criticalEigenvalue φ) n‖) ^ 2 ≤ C) :
    ∃ (M : ℕ) (C : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖) ^ 2 ≤ C := by
  obtain ⟨M17, C17, h17⟩ := h17U
  obtain ⟨a, ha, hxa⟩ := hloc
  obtain ⟨L, hL, hLb⟩ := hconst
  obtain ⟨r0, hr0, CT, hCT, hgerm⟩ := hgerm0
  refine ⟨M17 + (⌈a⌉₊ + ⌈2 * L + 1⌉₊ + 1 + ⌈2 * (a + L)⌉₊ + ⌈2 * L⌉₊ + ⌈1 / r0⌉₊),
    4 * (((1 + 2 * L) * (4 * L)) ^ 2 * (2 * C17 + 8 * L ^ 2 * (∑' n : ℤ, (1 / indexWeight n) ^ 2)) +
      ((1 + 2 * L) * 4) ^ 2 * (2 * C17 + 8 * L ^ 2 * (∑' n : ℤ, (1 / indexWeight n) ^ 2)) ^ 2 +
      ((1 + 2 * L) / 2) ^ 2 * C17 + (CT * 2 ^ (N + 2)) ^ 2 * (∑' n : ℤ, (1 / indexWeight n) ^ 2)),
    fun φ hφ F hF => ?_⟩
  obtain ⟨hJ, hLp, hLs, hI⟩ := hLb φ hφ
  obtain ⟨ζ, hζ⟩ := hgerm φ hφ
  have hE17 : ∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖critE N φ n‖) ^ 2 ≤ C17 := by
    have h := h17 φ hφ F (fun n hn => by have := hF n hn; push_cast at this ⊢; omega)
    unfold critE
    exact h
  refine sum_part F (fun n => indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖)
    (fun n => indexWeight n ^ (N + 1) * ‖critE N φ n‖) (fun n => 1 / indexWeight n) L _ _ _ _ C17 _
    (fun n _ => mul_nonneg (pow_nonneg (by linarith [KSPS015W.one_le_w n]) _) (norm_nonneg _))
    (fun n _ => mul_nonneg (pow_nonneg (by linarith [KSPS015W.one_le_w n]) _) (norm_nonneg _))
    (fun n _ => div_nonneg zero_le_one (by linarith [KSPS015W.one_le_w n])) hL
    (fun n hn => per_index N hN φ a ha (hxa φ hφ) L hL hJ hLp hLs hI r0 hr0 CT hCT ζ hζ n
      (by have := hF n hn; push_cast at this ⊢; omega))
    hE17 (KSPS016W.sq_summable_inv_w.sum_le_tsum F (fun n _ => sq_nonneg _))

end
end NlsGge.ThirdConsultation.KSPS025U10
