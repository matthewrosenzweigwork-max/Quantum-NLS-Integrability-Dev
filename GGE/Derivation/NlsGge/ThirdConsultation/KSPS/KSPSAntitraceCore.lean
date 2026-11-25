import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS016Host
import NlsGge.ThirdConsultation.KSPS.KSPS021Support
import NlsGge.ThirdConsultation.KSPS.KSPS014Support1
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU3
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU4

/- KSPSAT PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPSAntitraceCore.lean. Pro round-15 SUPPORT (never a packet). CORE of
   KSPS.antitrace_at_dirichlet_uniform (PRO_DEFINITION_RESPONSE_FP80_15.md Q5), route of proof development's
   ANTITRACE_UNIFORM_STOP.md "Assembly":
   * at ξ = μ the Dirichlet numerator vanishes (KSPS021W.dirichletNumerator_mu), so with s = 2i sin(wkbPhase),
     target = antitraceError − (β−α)(dirichletError + H + Z)/((1−α)(1−β))   (target_eq, exact algebra);
   * TAIL |n| ≥ J: |α|,|β| ≤ S(B₀)/(2|μ|) ≤ 1/2 (KSPSWKB.endpointSum_norm_le, |μ| ≥ threshold N B₀ = 1+S),
     so w^{N+1}|target| ≤ K(w^{N+1}|aErr| + w^{N+1}|dErr| + w^N|φ̂₁(−n)| + w^N|φ̂₂(n)| + 1/w) (tail_real);
   * LOW |n| < J (finitely many labels, bounded DIRECTLY from the definitions, not from tail producers):
     |target| ≤ |M₀₁|+|M₁₀|+|φ̂₁(−n)|+|φ̂₂(n)| ≤ 2exp(a+1+B₀²/2) + 2B₀ (GK38.norm_monodromyPair_entry_le,
     KSPSU4.potL1Norm38_le, KSPSU4.weighted_fourier_le), w ≤ J;
   * antitrace_of: the Pro r15 conclusion body, from (i) the uniform localization of μ and (ii) the uniform KSPS-016
     tail at ξ = μ as explicit hypotheses of exactly the KSPSU1.mu_localization_uniform body and the
     KSPS016U.boundary_tail_of conclusion body at ξ = μ φ (discharged in the glue module KSPSAntitraceUniform). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSAT
open NlsGge.ThirdConsultation.KSPSWKB

/-! ### Pure algebra -/

theorem target_eq (A G aE dE s α β H Z : ℂ) (hD : 1 - α * β ≠ 0) (hP : (1 - α) * (1 - β) ≠ 0)
    (ha : aE = A - ((β - α) / (1 - α * β) * s + G))
    (hd : dE = 0 - ((1 - α) * (1 - β) / (1 - α * β) * s + H + Z)) :
    A - G = aE - (β - α) * (dE + H + Z) / ((1 - α) * (1 - β)) := by
  have key : (β - α) * (0 - ((1 - α) * (1 - β) / (1 - α * β) * s + H + Z) + H + Z) / ((1 - α) * (1 - β)) =
      -((β - α) / (1 - α * β) * s) := by
    rw [div_eq_iff hP]
    ring
  rw [hd, key, ha]
  ring

theorem tail_real (N : ℕ) (t ae de f1 f2 il X q p w S0 CI : ℝ)
    (ht : t ≤ ae + q / p * (de + (f1 + f2) + 2 * il / (2 * X) ^ (N + 1)))
    (hq : q ≤ S0 / X) (hp : 1 / 4 ≤ p) (hwX : w ≤ 2 * X) (hw1 : 1 ≤ w) (hil0 : 0 ≤ il) (hil : il ≤ CI)
    (hS0 : 0 ≤ S0) (hq0 : 0 ≤ q) (hae : 0 ≤ ae) (hde : 0 ≤ de) (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2) :
    w ^ (N + 1) * t ≤ (1 + 8 * S0 + 16 * S0 * CI) *
      (w ^ (N + 1) * ae + w ^ (N + 1) * de + w ^ N * f1 + w ^ N * f2 + 1 / w) := by
  have hX0 : 0 < X := by linarith
  have hw0 : 0 < w := by linarith
  have hp0 : 0 < p := by linarith
  have hCI0 : 0 ≤ CI := hil0.trans hil
  have hW1 : 1 ≤ w ^ N := one_le_pow₀ hw1
  have hW0 : 0 < w ^ N := by positivity
  have hpw : w ^ (N + 1) = w ^ N * w := pow_succ w N
  have hqp : q / p ≤ 4 * S0 / X := by
    rw [div_le_div_iff₀ hp0 hX0]
    have h1 : q * X ≤ S0 := (le_div_iff₀ hX0).1 hq
    have h2 := mul_le_mul_of_nonneg_left hp hS0
    linarith
  have hZ : w ^ N * (2 * il / (2 * X) ^ (N + 1)) ≤ 2 * CI * (1 / w) := by
    have hpow : w ^ N * w ≤ (2 * X) ^ (N + 1) := by
      rw [← hpw]; exact pow_le_pow_left₀ hw0.le hwX _
    calc w ^ N * (2 * il / (2 * X) ^ (N + 1)) ≤ w ^ N * (2 * il / (w ^ N * w)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow)
            hW0.le
      _ = 2 * il * (1 / w) := by field_simp
      _ ≤ 2 * CI * (1 / w) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  set D := de + (f1 + f2) + 2 * il / (2 * X) ^ (N + 1) with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have h1 : w ^ N * w * t ≤ w ^ N * w * ae + w ^ N * w * (q / p) * D := by
    have := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ w ^ N * w)
    linarith [show w ^ N * w * (ae + q / p * D) = w ^ N * w * ae + w ^ N * w * (q / p) * D by ring]
  have hwX' : w / X ≤ 2 := by rw [div_le_iff₀ hX0]; linarith
  have h2 : w ^ N * w * (q / p) ≤ 8 * S0 * w ^ N := by
    calc w ^ N * w * (q / p) ≤ w ^ N * w * (4 * S0 / X) :=
          mul_le_mul_of_nonneg_left hqp (by positivity)
      _ = 4 * S0 * w ^ N * (w / X) := by field_simp
      _ ≤ 4 * S0 * w ^ N * 2 := mul_le_mul_of_nonneg_left hwX' (by positivity)
      _ = 8 * S0 * w ^ N := by ring
  have h3 : w ^ N * w * (q / p) * D ≤ 8 * S0 * w ^ N * D := mul_le_mul_of_nonneg_right h2 hD0
  have h4 : 8 * S0 * w ^ N * D ≤
      8 * S0 * (w ^ N * w * de + w ^ N * f1 + w ^ N * f2 + 2 * CI * (1 / w)) := by
    have e : 8 * S0 * w ^ N * D =
        8 * S0 * (w ^ N * de + w ^ N * f1 + w ^ N * f2 + w ^ N * (2 * il / (2 * X) ^ (N + 1))) := by
      rw [hD]; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hde' : w ^ N * de ≤ w ^ N * w * de := by
      have := mul_le_mul_of_nonneg_left hw1 (mul_nonneg hW0.le hde)
      calc w ^ N * de = w ^ N * de * 1 := by ring
        _ ≤ w ^ N * de * w := this
        _ = w ^ N * w * de := by ring
    linarith
  rw [hpw]
  have hSC : 0 ≤ S0 * CI := mul_nonneg hS0 hCI0
  set K := 1 + 8 * S0 + 16 * S0 * CI with hK
  have k1 : w ^ N * w * ae ≤ K * (w ^ N * w * ae) :=
    le_mul_of_one_le_left (by positivity) (by rw [hK]; linarith)
  have k2 : 8 * S0 * (w ^ N * w * de) ≤ K * (w ^ N * w * de) :=
    mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (by positivity)
  have k3 : 8 * S0 * (w ^ N * f1) ≤ K * (w ^ N * f1) :=
    mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (by positivity)
  have k4 : 8 * S0 * (w ^ N * f2) ≤ K * (w ^ N * f2) :=
    mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (by positivity)
  have k5 : 8 * S0 * (2 * CI * (1 / w)) ≤ K * (1 / w) := by
    rw [show 8 * S0 * (2 * CI * (1 / w)) = (16 * S0 * CI) * (1 / w) by ring]
    exact mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (by positivity)
  have e5 : K * (w ^ N * w * ae + w ^ N * w * de + w ^ N * f1 + w ^ N * f2 + 1 / w) =
      K * (w ^ N * w * ae) + K * (w ^ N * w * de) + K * (w ^ N * f1) + K * (w ^ N * f2) + K * (1 / w) := by
    ring
  have e6 : 8 * S0 * (w ^ N * w * de + w ^ N * f1 + w ^ N * f2 + 2 * CI * (1 / w)) =
      8 * S0 * (w ^ N * w * de) + 8 * S0 * (w ^ N * f1) + 8 * S0 * (w ^ N * f2) +
        8 * S0 * (2 * CI * (1 / w)) := by ring
  rw [e5]
  linarith

theorem sq_add5_le (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e),
    sq_nonneg (d - e)]

theorem sum_sq_le_five {ι : Type*} (F : Finset ι) (x t1 t2 t3 t4 t5 : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ n ∈ F, 0 ≤ x n ∧ x n ≤ K * (t1 n + t2 n + t3 n + t4 n + t5 n))
    (T1 T2 T3 T4 T5 : ℝ)
    (h1 : ∑ n ∈ F, t1 n ^ 2 ≤ T1) (h2 : ∑ n ∈ F, t2 n ^ 2 ≤ T2) (h3 : ∑ n ∈ F, t3 n ^ 2 ≤ T3)
    (h4 : ∑ n ∈ F, t4 n ^ 2 ≤ T4) (h5 : ∑ n ∈ F, t5 n ^ 2 ≤ T5) :
    ∑ n ∈ F, x n ^ 2 ≤ K ^ 2 * (5 * (T1 + T2 + T3 + T4 + T5)) := by
  have hp : ∀ n ∈ F, x n ^ 2 ≤
      K ^ 2 * (5 * (t1 n ^ 2 + t2 n ^ 2 + t3 n ^ 2 + t4 n ^ 2 + t5 n ^ 2)) := by
    intro n hn
    obtain ⟨h0, hle⟩ := h n hn
    calc x n ^ 2 ≤ (K * (t1 n + t2 n + t3 n + t4 n + t5 n)) ^ 2 := pow_le_pow_left₀ h0 hle 2
      _ = K ^ 2 * (t1 n + t2 n + t3 n + t4 n + t5 n) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (sq_add5_le _ _ _ _ _) (sq_nonneg K)
  refine (Finset.sum_le_sum hp).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
  linarith

/-! ### Per-index facts -/

theorem one_le_w (n : ℤ) : 1 ≤ indexWeight n := NlsGge.ThirdConsultation.KSPS015W.one_le_w n

theorem fourier_le_B {N : ℕ} (φ : SobolevC N) {B₀ : ℝ} (hB₀ : 0 ≤ B₀) (hφ : sobolevNorm N φ ≤ B₀) (n : ℤ) :
    ‖physicalFourier (toPotPair φ).1 (-n)‖ ≤ B₀ ∧ ‖physicalFourier (toPotPair φ).2 n‖ ≤ B₀ := by
  have hW := NlsGge.ThirdConsultation.KSPSU4.weighted_fourier_le N φ {n}
  simp only [Finset.sum_singleton] at hW
  have hs0 : 0 ≤ sobolevNorm N φ := by unfold sobolevNorm; exact Real.sqrt_nonneg _
  have hB2 : sobolevNorm N φ ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ hs0 hφ 2
  have hW1 : 1 ≤ indexWeight n ^ N := one_le_pow₀ (one_le_w n)
  have k1 : (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖) ^ 2 ≤ B₀ ^ 2 := by
    nlinarith [sq_nonneg (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖)]
  have k2 : (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖) ^ 2 ≤ B₀ ^ 2 := by
    nlinarith [sq_nonneg (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖)]
  have l1 := (pow_le_pow_iff_left₀ (by positivity) hB₀ (by norm_num : (2 : ℕ) ≠ 0)).1 k1
  have l2 := (pow_le_pow_iff_left₀ (by positivity) hB₀ (by norm_num : (2 : ℕ) ≠ 0)).1 k2
  exact ⟨(le_mul_of_one_le_left (norm_nonneg _) hW1).trans l1,
    (le_mul_of_one_le_left (norm_nonneg _) hW1).trans l2⟩

theorem low_bound {N : ℕ} (φ : SobolevC N) {B₀ a : ℝ} (hB₀ : 0 ≤ B₀) (ha : 0 ≤ a)
    (hφ : sobolevNorm N φ ≤ B₀) (n : ℤ)
    (hmu : ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) :
    ‖KSPSWKB.antitrace φ (mu φ n) -
        Complex.I * (-1 : ℂ) ^ n *
          (physicalFourier (toPotPair φ).1 (-n) - physicalFourier (toPotPair φ).2 n)‖ ≤
      2 * Real.exp (a + (1 + B₀ ^ 2 / 2)) + 2 * B₀ := by
  have hw1 := one_le_w n
  have him : |(mu φ n).im| ≤ a := by
    have e : (mu φ n).im = (mu φ n - (n : ℂ) * (Real.pi : ℂ)).im := by simp
    rw [e]
    refine (Complex.abs_im_le_norm _).trans (hmu.trans ?_)
    exact div_le_self ha hw1
  have hL1 := NlsGge.ThirdConsultation.KSPSU4.potL1Norm38_le N φ
  have hs0 : 0 ≤ sobolevNorm N φ := by unfold sobolevNorm; exact Real.sqrt_nonneg _
  have hB2 : sobolevNorm N φ ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ hs0 hφ 2
  have hE : ∀ i j : Fin 2, ‖monodromyPair (toPotPair φ) (mu φ n) i j‖ ≤ Real.exp (a + (1 + B₀ ^ 2 / 2)) :=
    fun i j => (norm_monodromyPair_entry_le (toPotPair φ) (mu φ n) i j).trans
      (Real.exp_le_exp.2 (by linarith))
  obtain ⟨hF1, hF2⟩ := fourier_le_B φ hB₀ hφ n
  have hsg : ‖Complex.I * (-1 : ℂ) ^ n‖ = 1 := by
    rw [norm_mul, Complex.norm_I, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
  unfold KSPSWKB.antitrace
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, hsg, one_mul]
  have h1 := norm_add_le (monodromyPair (toPotPair φ) (mu φ n) 0 1) (monodromyPair (toPotPair φ) (mu φ n) 1 0)
  have h2 := norm_sub_le (physicalFourier (toPotPair φ).1 (-n)) (physicalFourier (toPotPair φ).2 n)
  linarith [hE 0 1, hE 1 0]

theorem tail_pointwise {N : ℕ} (φ : SobolevC N) {B₀ a CI : ℝ} (ha : 0 ≤ a)
    (hφ : sobolevNorm N φ ≤ B₀) (hIL : ‖integralRiccatiLeft φ (N + 1)‖ ≤ CI)
    (hmu : ∀ n : ℤ, ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) (n : ℤ)
    (hn : ((⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀⌉₊ + 1 : ℕ) : ℤ) ≤ |n|) :
    indexWeight n ^ (N + 1) * ‖KSPSWKB.antitrace φ (mu φ n) -
        Complex.I * (-1 : ℂ) ^ n *
          (physicalFourier (toPotPair φ).1 (-n) - physicalFourier (toPotPair φ).2 n)‖ ≤
      (1 + 8 * (∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k) +
          16 * (∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k) * CI) *
        (indexWeight n ^ (N + 1) * ‖KSPSWKB.antitraceError N φ (mu φ) n‖ +
          indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ (mu φ) n‖ +
          indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖ +
          indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖ + 1 / indexWeight n) := by
  set S0 := ∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k
    with hS0
  have hS00 : 0 ≤ S0 := Finset.sum_nonneg (fun k hk => endpointCoefficientBound_nonneg N B₀ k hk)
  obtain ⟨hX1, hXT, hwX⟩ := NlsGge.ThirdConsultation.KSPS015W.tail_facts a _ ha (mu φ) hmu n hn
  have hT : NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀ = 1 + S0 := rfl
  rw [hT] at hXT
  set μ := mu φ n with hμ
  have hX0 : 0 < ‖μ‖ := by linarith
  have hα : ‖alpha φ μ 0‖ ≤ S0 / (2 * ‖μ‖) := endpointSum_norm_le B₀ φ hφ false μ hX1
  have hβ : ‖beta φ μ 0‖ ≤ S0 / (2 * ‖μ‖) := endpointSum_norm_le B₀ φ hφ true μ hX1
  have hhalf : S0 / (2 * ‖μ‖) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  set α := alpha φ μ 0 with hαd
  set β := beta φ μ 0 with hβd
  have hα2 : ‖α‖ ≤ 1 / 2 := hα.trans hhalf
  have hβ2 : ‖β‖ ≤ 1 / 2 := hβ.trans hhalf
  have hD : 1 - α * β ≠ 0 := by
    intro h
    have h1 : α * β = 1 := by linear_combination -h
    have : ‖α * β‖ ≤ 1 / 4 := by
      rw [norm_mul]; nlinarith [norm_nonneg α, norm_nonneg β]
    rw [h1, norm_one] at this; norm_num at this
  have h1a : 1 / 2 ≤ ‖1 - α‖ := by
    have := norm_sub_norm_le (1 : ℂ) α; rw [norm_one] at this; linarith
  have h1b : 1 / 2 ≤ ‖1 - β‖ := by
    have := norm_sub_norm_le (1 : ℂ) β; rw [norm_one] at this; linarith
  have hPn : 1 / 4 ≤ ‖(1 - α) * (1 - β)‖ := by
    rw [norm_mul]; nlinarith
  have hP : (1 - α) * (1 - β) ≠ 0 := by
    intro h; rw [h, norm_zero] at hPn; norm_num at hPn
  have hq : ‖β - α‖ ≤ S0 / ‖μ‖ := by
    have := norm_sub_le β α
    have e : S0 / ‖μ‖ = S0 / (2 * ‖μ‖) + S0 / (2 * ‖μ‖) := by field_simp; ring
    linarith
  -- the exact identity at the Dirichlet root
  set s := 2 * Complex.I * Complex.sin (wkbPhase φ μ) with hs
  set F1 := physicalFourier (toPotPair φ).1 (-n) with hF1
  set F2 := physicalFourier (toPotPair φ).2 n with hF2
  set IL := integralRiccatiLeft φ (N + 1) with hIL'
  set H := Complex.I * (-1 : ℂ) ^ (n + 1) * (F1 + F2) with hH
  set Z := 2 * (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * μ) ^ (N + 1) * IL with hZ
  have ha' : KSPSWKB.antitraceError N φ (mu φ) n =
      KSPSWKB.antitrace φ μ - ((β - α) / (1 - α * β) * s + Complex.I * (-1 : ℂ) ^ n * (F1 - F2)) := rfl
  have hd' : KSPSWKB.dirichletError N φ (mu φ) n =
      0 - ((1 - α) * (1 - β) / (1 - α * β) * s + H + Z) := by
    have hd0 : KSPSWKB.dirichletNumerator φ μ = 0 := NlsGge.ThirdConsultation.KSPS021W.dirichletNumerator_mu φ n
    rw [show KSPSWKB.dirichletError N φ (mu φ) n =
      KSPSWKB.dirichletNumerator φ μ - ((1 - α) * (1 - β) / (1 - α * β) * s + H + Z) from rfl, hd0]
  have heq := target_eq (KSPSWKB.antitrace φ μ) (Complex.I * (-1 : ℂ) ^ n * (F1 - F2))
    (KSPSWKB.antitraceError N φ (mu φ) n) (KSPSWKB.dirichletError N φ (mu φ) n) s α β H Z hD hP ha' hd'
  rw [heq]
  -- norms
  have hsg1 : ‖Complex.I * (-1 : ℂ) ^ (n + 1)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
  have hHn : ‖H‖ ≤ ‖F1‖ + ‖F2‖ := by
    rw [hH, norm_mul, hsg1, one_mul]; exact norm_add_le _ _
  have hZn : ‖Z‖ = 2 * ‖IL‖ / (2 * ‖μ‖) ^ (N + 1) := by
    rw [hZ, norm_mul, norm_div, norm_mul, norm_pow, norm_mul, norm_mul, Complex.norm_I,
      norm_zpow, norm_neg, norm_one, one_zpow, Complex.norm_ofNat]
    ring
  have ht : ‖KSPSWKB.antitraceError N φ (mu φ) n -
        (β - α) * (KSPSWKB.dirichletError N φ (mu φ) n + H + Z) / ((1 - α) * (1 - β))‖ ≤
      ‖KSPSWKB.antitraceError N φ (mu φ) n‖ + ‖β - α‖ / ‖(1 - α) * (1 - β)‖ *
        (‖KSPSWKB.dirichletError N φ (mu φ) n‖ + (‖F1‖ + ‖F2‖) + 2 * ‖IL‖ / (2 * ‖μ‖) ^ (N + 1)) := by
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_div, norm_mul, mul_div_right_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← hZn]
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le (KSPSWKB.dirichletError N φ (mu φ) n) H
    linarith
  have hw1 := one_le_w n
  exact tail_real N _ _ _ _ _ _ _ _ _ _ _ _ ht hq hPn hwX hw1 (norm_nonneg _) hIL hS00 (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)

/-! ### Assembly -/

theorem rpow_weight (N : ℕ) (n : ℤ) (x : ℝ) :
    indexWeight n ^ (2 * ((N + 1 : ℕ) : ℝ)) * x ^ 2 = (indexWeight n ^ (N + 1) * x) ^ 2 := by
  rw [show (2 * ((N + 1 : ℕ) : ℝ)) = ((2 * (N + 1) : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  ring

theorem antitrace_of (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (a : ℝ) (ha : 0 ≤ a)
    (hmu : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ n : ℤ, ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (N0 : ℕ) (CT : ℝ) (hCT : 0 ≤ CT)
    (hT : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ F : Finset ℤ, (∀ n ∈ F, (N0 : ℤ) ≤ |n|) →
        (∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖KSPSWKB.antitraceError N φ (mu φ) n‖) ^ 2 ≤ CT) ∧
        (∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ (mu φ) n‖) ^ 2 ≤ CT)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => KSPSWKB.antitrace φ (mu φ n) -
            Complex.I * (-1 : ℂ)^n *
              (physicalFourier (toPotPair φ).1 (-n) -
               physicalFourier (toPotPair φ).2 n)) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖KSPSWKB.antitrace φ (mu φ n) -
                Complex.I * (-1 : ℂ)^n *
                  (physicalFourier (toPotPair φ).1 (-n) -
                   physicalFourier (toPotPair φ).2 n)‖)^2) ≤ C^2 := by
  obtain ⟨CI, hCI0, hIb⟩ := NlsGge.ThirdConsultation.KSPSU3.integralRiccatiLeft_uniform N hN B₀ hB₀
  obtain ⟨S0, hS0⟩ : ∃ S0 : ℝ, S0 = ∑ k ∈ Finset.Icc 1 N,
      NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k := ⟨_, rfl⟩
  have hS00 : 0 ≤ S0 := by
    rw [hS0]; exact Finset.sum_nonneg (fun k hk => endpointCoefficientBound_nonneg N B₀ k hk)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 1 + 8 * S0 + 16 * S0 * CI := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨Sv, hSv⟩ : ∃ Sv : ℝ, Sv = ∑' n : ℤ, (1 / indexWeight n) ^ 2 := ⟨_, rfl⟩
  have hSv0 : 0 ≤ Sv := by rw [hSv]; exact tsum_nonneg (fun n => sq_nonneg _)
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = max N0 (⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀⌉₊ + 1) :=
    ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * Real.exp (a + (1 + B₀ ^ 2 / 2)) + 2 * B₀ := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  obtain ⟨Ctot, hCtot⟩ : ∃ Ctot : ℝ,
      Ctot = K ^ 2 * (5 * (CT + CT + B₀ ^ 2 + B₀ ^ 2 + Sv)) + (2 * (J : ℝ)) * (((J : ℝ) ^ (N + 1) * M) ^ 2) :=
    ⟨_, rfl⟩
  have hCtot0 : 0 ≤ Ctot := by rw [hCtot]; positivity
  have hJ0 : N0 ≤ J := by rw [hJ]; exact le_max_left _ _
  have hJT : ⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀⌉₊ + 1 ≤ J := by
    rw [hJ]; exact le_max_right _ _
  -- the finite-sum bound
  have key : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ F : Finset ℤ,
      ∑ n ∈ F, (indexWeight n ^ (N + 1) *
        ‖KSPSWKB.antitrace φ (mu φ n) -
          Complex.I * (-1 : ℂ) ^ n *
            (physicalFourier (toPotPair φ).1 (-n) - physicalFourier (toPotPair φ).2 n)‖) ^ 2 ≤ Ctot := by
    intro φ hφ F
    have hI := hIb φ hφ (N + 1) (by omega) le_rfl
    set x : ℤ → ℝ := fun n => indexWeight n ^ (N + 1) *
        ‖KSPSWKB.antitrace φ (mu φ n) -
          Complex.I * (-1 : ℂ) ^ n *
            (physicalFourier (toPotPair φ).1 (-n) - physicalFourier (toPotPair φ).2 n)‖ with hx
    rw [← Finset.sum_filter_add_sum_filter_not F (fun n : ℤ => (J : ℤ) ≤ |n|)]
    -- tail
    have hTail : ∑ n ∈ F.filter (fun n : ℤ => (J : ℤ) ≤ |n|), x n ^ 2 ≤
        K ^ 2 * (5 * (CT + CT + B₀ ^ 2 + B₀ ^ 2 + Sv)) := by
      have hF0 : ∀ n ∈ F.filter (fun n : ℤ => (J : ℤ) ≤ |n|), (N0 : ℤ) ≤ |n| := fun n hn =>
        le_trans (Nat.cast_le.mpr hJ0) (Finset.mem_filter.mp hn).2
      obtain ⟨hTa, hTd⟩ := hT φ hφ _ hF0
      have hW := NlsGge.ThirdConsultation.KSPSU4.weighted_fourier_le N φ (F.filter (fun n : ℤ => (J : ℤ) ≤ |n|))
      have hs0 : 0 ≤ sobolevNorm N φ := by unfold sobolevNorm; exact Real.sqrt_nonneg _
      have hB2 : sobolevNorm N φ ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ hs0 hφ 2
      have p1 : 0 ≤ ∑ n ∈ F.filter (fun n : ℤ => (J : ℤ) ≤ |n|),
          (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖) ^ 2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have p2 : 0 ≤ ∑ n ∈ F.filter (fun n : ℤ => (J : ℤ) ≤ |n|),
          (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖) ^ 2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hsv : ∑ n ∈ F.filter (fun n : ℤ => (J : ℤ) ≤ |n|), (1 / indexWeight n) ^ 2 ≤ Sv := by
        rw [hSv]
        exact NlsGge.ThirdConsultation.KSPS016W.sq_summable_inv_w.sum_le_tsum _ (fun n _ => sq_nonneg _)
      refine sum_sq_le_five _ x
        (fun n => indexWeight n ^ (N + 1) * ‖KSPSWKB.antitraceError N φ (mu φ) n‖)
        (fun n => indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ (mu φ) n‖)
        (fun n => indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖)
        (fun n => indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖)
        (fun n => 1 / indexWeight n) K hK0 ?_ _ _ _ _ _ hTa hTd (by beta_reduce; linarith)
        (by beta_reduce; linarith) hsv
      intro n hn
      beta_reduce
      have hnJ := (Finset.mem_filter.mp hn).2
      have hnT : ((⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀⌉₊ + 1 : ℕ) : ℤ) ≤ |n| :=
        le_trans (Nat.cast_le.mpr hJT) hnJ
      have hw0 : 0 < indexWeight n := lt_of_lt_of_le one_pos (one_le_w n)
      refine ⟨by simp only [hx]; positivity, ?_⟩
      have h := tail_pointwise φ ha hφ hI (hmu φ hφ) n hnT
      rw [← hS0, ← hK] at h
      exact h
    -- low labels
    have hLow : ∑ n ∈ F.filter (fun n : ℤ => ¬ (J : ℤ) ≤ |n|), x n ^ 2 ≤
        (2 * (J : ℝ)) * (((J : ℝ) ^ (N + 1) * M) ^ 2) := by
      have hpt : ∀ n ∈ F.filter (fun n : ℤ => ¬ (J : ℤ) ≤ |n|), x n ^ 2 ≤ ((J : ℝ) ^ (N + 1) * M) ^ 2 := by
        intro n hn
        have hnJ : |n| < (J : ℤ) := lt_of_not_ge (Finset.mem_filter.mp hn).2
        have hnJ' : |n| + 1 ≤ (J : ℤ) := Int.add_one_le_of_lt hnJ
        have hR : |(n : ℝ)| + 1 ≤ (J : ℝ) := by
          have : ((|n| + 1 : ℤ) : ℝ) ≤ ((J : ℤ) : ℝ) := Int.cast_le.2 hnJ'
          push_cast at this
          exact this
        have hw0 : 0 < indexWeight n := lt_of_lt_of_le one_pos (one_le_w n)
        have hwJ : indexWeight n ≤ (J : ℝ) := by
          unfold indexWeight
          rw [Real.sqrt_le_iff]
          refine ⟨by positivity, ?_⟩
          have : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
          rw [this]
          nlinarith [abs_nonneg (n : ℝ)]
        have hb := low_bound φ hB₀ ha hφ n (hmu φ hφ n)
        rw [← hM] at hb
        have hx0 : 0 ≤ x n := by simp only [hx]; positivity
        have hxb : x n ≤ (J : ℝ) ^ (N + 1) * M := by
          simp only [hx]
          exact mul_le_mul (pow_le_pow_left₀ hw0.le hwJ _) hb (norm_nonneg _) (by positivity)
        exact pow_le_pow_left₀ hx0 hxb 2
      refine (Finset.sum_le_sum hpt).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hsub : F.filter (fun n : ℤ => ¬ (J : ℤ) ≤ |n|) ⊆ Finset.Ioo (-(J : ℤ)) (J : ℤ) := by
        intro n hn
        have hnJ : |n| < (J : ℤ) := lt_of_not_ge (Finset.mem_filter.mp hn).2
        rw [Finset.mem_Ioo]
        exact abs_lt.mp hnJ
      have hc := Finset.card_le_card hsub
      rw [Int.card_Ioo] at hc
      have hc2 : ((J : ℤ) - -(J : ℤ) - 1).toNat ≤ 2 * J := Int.toNat_le.mpr (by push_cast; omega)
      have hc' : (F.filter (fun n : ℤ => ¬ (J : ℤ) ≤ |n|)).card ≤ 2 * J := hc.trans hc2
      have : ((F.filter (fun n : ℤ => ¬ (J : ℤ) ≤ |n|)).card : ℝ) ≤ ((2 * J : ℕ) : ℝ) := Nat.cast_le.mpr hc'
      push_cast at this
      exact this
    rw [hCtot]
    exact add_le_add hTail hLow
  refine ⟨Real.sqrt Ctot, Real.sqrt_nonneg _, fun φ hφ => ⟨?_, ?_⟩⟩
  · unfold WeightedL2Error
    refine summable_of_sum_le (c := Ctot) (fun n => by
      show (0 : ℝ) ≤ _
      exact mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (one_le_w n)) _) (sq_nonneg _)) (fun F => ?_)
    have h := key φ hφ F
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl (fun n _ => ?_)
    exact rpow_weight N n _
  · intro F
    rw [Real.sq_sqrt hCtot0]
    exact key φ hφ F

end NlsGge.ThirdConsultation.KSPSAT
