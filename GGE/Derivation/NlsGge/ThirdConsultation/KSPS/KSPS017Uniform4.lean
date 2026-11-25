import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS017Support3
import NlsGge.ThirdConsultation.KSPS.KSPS016Support
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU4
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform0

/- KSPS017U4 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS017Uniform4.lean. Pro round-15 SUPPORT (never a packet), input h17U.
   Ball-uniform TAIL companion of KSPS017W.discriminant_derivative_WKB_of (KSPS-017 assembly): for one cutoff M and one
   constant C, both fixed before φ (sobolevNorm N φ ≤ B₀), ξ (‖ξ_n − nπ‖ ≤ a/w_n) and F (|n| ≥ M),
     Σ_F (w_n^{N+1} ‖Δ'(ξ_n) − discriminantDerivativeMain‖)² ≤ C.
   Route = landed Support3 body (exact KSPS-015 identity on the open tail, product rule, pure_bound), with
   B := B₀ in endpointSum_norm_le / initialColumns_det_bound (S = Σ endpointCoefficientBound N B₀ k), the per-φ KA/KB of
   endpointCoeff_deriv replaced by the explicit Σ k·endpointCoefficientBound N B₀ k (coefficientTraceZero_le_bound),
   and every Summable dominating sequence replaced by a finite sum with an explicit bound. The inputs are the
   ball-uniform tail forms of KSPS-011 (endpoint_remainder_tail_U), KSPS-012 (KSPSUG.diag_*_tail_U), the
   differentiated remainders (KSPS017U1/U2 instantiated), KSPS-013, KSPS-014 (B = B₀) and the uniform bound of the
   Riccati integral (KSPSU3.integralRiccatiLeft_uniform), taken as hypotheses with the exact types the glue discharges.
   No hypothesis is added to any stated target. -/
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS017U4
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS017W
open NlsGge.ThirdConsultation.KSPSWKB

/-- Support3.disc_eventuallyEq with the KSPS-014 radius B₀ ≥ sobolevNorm N φ. -/
theorem disc_eventuallyEq_U {N : ℕ} (φ : SobolevC N) (B₀ : ℝ) (hφ : sobolevNorm N φ ≤ B₀)
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (h14 : ∀ lam : {z : ℂ // z ≠ 0}, WKBThreshold N B₀ lam.1 →
      monodromyPair (toPotPair φ) lam.1 = NlsGge.ThirdConsultation.KSPSWKB.explicitWKBMonodromy N φ lam)
    {xi0 : ℂ} (hxi0 : NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀ < ‖xi0‖) :
    discriminant φ =ᶠ[𝓝 xi0] fun z : ℂ => 2 * Complex.cos (wkbPhase φ z) +
      (1 - NlsGge.ThirdConsultation.KSPSWKB.beta φ z 0 * NlsGge.ThirdConsultation.KSPSWKB.alpha φ z 0)⁻¹ *
        (((2 * Complex.I * z) ^ N)⁻¹ *
          (Rfun φ false 0 z + Rfun φ true 1 z - NlsGge.ThirdConsultation.KSPSWKB.alpha φ z 0 * Rfun φ true 0 z -
            NlsGge.ThirdConsultation.KSPSWKB.beta φ z 0 * Rfun φ false 1 z)) := by
  have hopen : IsOpen {z : ℂ | NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀ < ‖z‖} :=
    isOpen_lt continuous_const continuous_norm
  have hT1 : 1 ≤ NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀ := by
    unfold NlsGge.ThirdConsultation.KSPSVolterra.threshold
    have := Finset.sum_nonneg (fun k hk => NlsGge.ThirdConsultation.KSPSWKB.endpointCoefficientBound_nonneg N B₀ k hk)
    linarith
  filter_upwards [hopen.mem_nhds hxi0] with z hz
  have hz' : NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀ < ‖z‖ := hz
  have hzpos : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hzpos; exact lt_irrefl _ hzpos
  have hthr : WKBThreshold N B₀ z := ⟨hzpos, hz'.le⟩
  have hdet := NlsGge.ThirdConsultation.KSPSWKB.initialColumns_det_bound N B₀ φ z hφ hthr
  have hdetv : Matrix.det (NlsGge.ThirdConsultation.KSPSWKB.initialColumns φ z) =
      1 - NlsGge.ThirdConsultation.KSPSWKB.beta φ z 0 * NlsGge.ThirdConsultation.KSPSWKB.alpha φ z 0 := by
    simp [NlsGge.ThirdConsultation.KSPSWKB.initialColumns, Matrix.det_fin_two]
  rw [hdetv] at hdet
  have hD : 1 - NlsGge.ThirdConsultation.KSPSWKB.beta φ z 0 * NlsGge.ThirdConsultation.KSPSWKB.alpha φ z 0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hdet; norm_num at hdet
  have hid := NlsGge.ThirdConsultation.KSPS015W.disc_identity φ ⟨z, hz0⟩ h13 (h14 ⟨z, hz0⟩ hthr) hD
  have e1 : Rfun φ false 0 z = NlsGge.ThirdConsultation.KSPS015W.rf φ ⟨z, hz0⟩ 0 := by unfold Rfun; rw [dif_neg hz0]; rfl
  have e2 : Rfun φ true 1 z = NlsGge.ThirdConsultation.KSPS015W.rt φ ⟨z, hz0⟩ 1 := by unfold Rfun; rw [dif_neg hz0]; rfl
  have e3 : Rfun φ true 0 z = NlsGge.ThirdConsultation.KSPS015W.rt φ ⟨z, hz0⟩ 0 := by unfold Rfun; rw [dif_neg hz0]; rfl
  have e4 : Rfun φ false 1 z = NlsGge.ThirdConsultation.KSPS015W.rf φ ⟨z, hz0⟩ 1 := by unfold Rfun; rw [dif_neg hz0]; rfl
  rw [e1, e2, e3, e4]
  linear_combination hid

/-- endpointCoeff_deriv with the B₀-uniform constant Σ k·endpointCoefficientBound N B₀ k. -/
theorem coeff_deriv_U {N : ℕ} (φ : SobolevC N) (B₀ : ℝ) (hφ : sobolevNorm N φ ≤ B₀) (b : Bool)
    (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ∃ d : ℂ, HasDerivAt (fun w : ℂ => -Complex.I * ∑ k ∈ Finset.Icc 1 N,
        ((2 * Complex.I * w) ^ k)⁻¹ * NlsGge.ThirdConsultation.KSPSWKB.coefficientTrace φ b k 0) d z ∧
      ‖d‖ ≤ (∑ k ∈ Finset.Icc 1 N, (k : ℝ) *
        NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k) / ‖z‖ ^ 2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; norm_num at hz
  refine ⟨_, (hasDerivAt_invPowSum N (fun k => NlsGge.ThirdConsultation.KSPSWKB.coefficientTrace φ b k 0) hz0).const_mul (-Complex.I), ?_⟩
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  refine (norm_invPowSum_deriv_le N _ hz).trans ?_
  have hz2 : 0 < ‖z‖ ^ 2 := by positivity
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum (fun k hk => ?_)) hz2.le
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg k)
  rw [NlsGge.ThirdConsultation.KSPSWKB.coefficientTrace_at_zero]
  exact NlsGge.ThirdConsultation.KSPSWKB.coefficientTraceZero_le_bound B₀ φ hφ b k hk

/-- Fourier tail sums of the N-th derivatives (|n| ≥ 1): Σ_F |F(∂^N φ)|² ≤ (2π)^{2N} B₀². -/
theorem fourier_iter_sums_le {N : ℕ} (φ : SobolevC N) {B₀ : ℝ} (hφ : sobolevNorm N φ ≤ B₀) (F : Finset ℤ)
    (hF : ∀ n ∈ F, 1 ≤ |(n : ℝ)|) :
    ∑ n ∈ F, ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ^ 2 ≤ ((2 * Real.pi) ^ N) ^ 2 * B₀ ^ 2 ∧
    ∑ n ∈ F, ‖physicalFourier (iteratedDerivative N φ.2) n‖ ^ 2 ≤ ((2 * Real.pi) ^ N) ^ 2 * B₀ ^ 2 := by
  have hW := NlsGge.ThirdConsultation.KSPSU4.weighted_fourier_le N φ F
  have hs0 : 0 ≤ sobolevNorm N φ := by unfold sobolevNorm; exact Real.sqrt_nonneg _
  have hB2 : sobolevNorm N φ ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ hs0 hφ 2
  have hpt : ∀ n ∈ F,
      ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ^ 2 ≤
        ((2 * Real.pi) ^ N) ^ 2 * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖) ^ 2 ∧
      ‖physicalFourier (iteratedDerivative N φ.2) n‖ ^ 2 ≤
        ((2 * Real.pi) ^ N) ^ 2 * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖) ^ 2 := by
    intro n hn
    obtain ⟨hDF1, hDF2, -, -⟩ := NlsGge.ThirdConsultation.KSPS016W.fourier_facts φ n (hF n hn)
    have hpn : ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N‖ = (2 * Real.pi * |(n : ℝ)|) ^ N := by
      rw [norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_intCast, mul_one]
    have hw : |(n : ℝ)| ≤ indexWeight n := by
      unfold indexWeight; exact Real.abs_le_sqrt (by linarith [sq_nonneg (n : ℝ)])
    have hle : (2 * Real.pi * |(n : ℝ)|) ^ N ≤ (2 * Real.pi) ^ N * indexWeight n ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hw (by positivity)) N
    have hsNn : ‖(-1 : ℂ) ^ N‖ = 1 := by rw [norm_pow, norm_neg, norm_one, one_pow]
    have a1 : ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ≤
        (2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖) := by
      rw [hDF1, norm_mul, norm_mul, hpn, hsNn, one_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    have a2 : ‖physicalFourier (iteratedDerivative N φ.2) n‖ ≤
        (2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖) := by
      rw [hDF2, norm_mul, hpn, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    constructor
    · exact (pow_le_pow_left₀ (norm_nonneg _) a1 2).trans (le_of_eq (by ring))
    · exact (pow_le_pow_left₀ (norm_nonneg _) a2 2).trans (le_of_eq (by ring))
  have h1 : 0 ≤ ∑ n ∈ F, (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0 ≤ ∑ n ∈ F, (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hP : 0 ≤ ((2 * Real.pi) ^ N) ^ 2 := sq_nonneg _
  constructor
  · refine (Finset.sum_le_sum (fun n hn => (hpt n hn).1)).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (by linarith) hP
  · refine (Finset.sum_le_sum (fun n hn => (hpt n hn).2)).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (by linarith) hP

/-- The pointwise Support3 estimate with B₀-uniform constants, from clean per-index bounds. -/
theorem pointwise_U (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (φ : SobolevC N) (hφ : sobolevNorm N φ ≤ B₀)
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (h14 : ∀ lam : {z : ℂ // z ≠ 0}, WKBThreshold N B₀ lam.1 →
      monodromyPair (toPotPair φ) lam.1 = NlsGge.ThirdConsultation.KSPSWKB.explicitWKBMonodromy N φ lam)
    (xi : ℤ → ℂ) (n : ℤ) (hX1 : 1 ≤ ‖xi n‖) (hXT : NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀ + 1 ≤ ‖xi n‖)
    (hwX : indexWeight n ≤ 2 * ‖xi n‖) (CI : ℝ) (hCI : ‖integralRiccatiLeft φ (N + 1)‖ ≤ CI)
    (Pc U V FU FL G : ℝ) (hPc : 0 ≤ Pc) (hG : 0 ≤ G)
    (hu : ‖Rfun φ true 0 (xi n)‖ ≤ U) (hv : ‖Rfun φ false 1 (xi n)‖ ≤ V)
    (hs : ‖Rfun φ false 0 (xi n) + Rfun φ true 1 (xi n)‖ ≤ Pc / indexWeight n)
    (hpp : ‖deriv (Rfun φ false 0) (xi n) + deriv (Rfun φ true 1) (xi n) -
      -2 * Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1)‖ ≤
        G / indexWeight n)
    (hp10 : ‖deriv (Rfun φ true 0) (xi n)‖ ≤ FU) (hp01 : ‖deriv (Rfun φ false 1) (xi n)‖ ≤ FL) :
    indexWeight n ^ (N + 1) *
        ‖deriv (discriminant φ) (xi n) - NlsGge.ThirdConsultation.KSPSWKB.discriminantDerivativeMain N φ xi n‖ ≤
      (4 * (2 * ∑ k ∈ Finset.Icc 1 N, (k : ℝ) *
          NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k) *
          (∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k) +
        2 * N + 4 * (2 * ∑ k ∈ Finset.Icc 1 N, (k : ℝ) *
          NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k) +
        2 * (∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k) +
        2 * (∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k) ^ 2 + 1) *
      ((Pc + (∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k) *
          (U + V)) + U + V + FU + FL + CI / indexWeight n + G) := by
  set S : ℝ := ∑ k ∈ Finset.Icc 1 N,
    NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun k hk => NlsGge.ThirdConsultation.KSPSWKB.endpointCoefficientBound_nonneg N B₀ k hk)
  set K1 : ℝ := ∑ k ∈ Finset.Icc 1 N, (k : ℝ) *
    NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k with hK1def
  have hK10 : 0 ≤ K1 := Finset.sum_nonneg (fun k hk =>
    mul_nonneg (Nat.cast_nonneg k) (NlsGge.ThirdConsultation.KSPSWKB.endpointCoefficientBound_nonneg N B₀ k hk))
  set K : ℝ := 2 * K1 with hKdef
  have hK0 : 0 ≤ K := by positivity
  set T : ℝ := NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀ with hTdef
  have hz : xi n ≠ 0 := by
    intro h; rw [h, norm_zero] at hX1; norm_num at hX1
  set ξ : ℂ := xi n with hξ
  set X : ℝ := ‖ξ‖ with hXdef
  set w : ℝ := indexWeight n with hwdef
  have hX0 : 0 < X := by linarith
  have hthr : WKBThreshold N B₀ ξ := ⟨hX0, by linarith⟩
  have hdet := NlsGge.ThirdConsultation.KSPSWKB.initialColumns_det_bound N B₀ φ ξ hφ hthr
  have hdetv : Matrix.det (NlsGge.ThirdConsultation.KSPSWKB.initialColumns φ ξ) =
      1 - NlsGge.ThirdConsultation.KSPSWKB.beta φ ξ 0 * NlsGge.ThirdConsultation.KSPSWKB.alpha φ ξ 0 := by
    simp [NlsGge.ThirdConsultation.KSPSWKB.initialColumns, Matrix.det_fin_two]
  rw [hdetv] at hdet
  have hD : 1 - NlsGge.ThirdConsultation.KSPSWKB.beta φ ξ 0 * NlsGge.ThirdConsultation.KSPSWKB.alpha φ ξ 0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hdet; norm_num at hdet
  have hDinv : ‖(1 - NlsGge.ThirdConsultation.KSPSWKB.beta φ ξ 0 * NlsGge.ThirdConsultation.KSPSWKB.alpha φ ξ 0)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hpos : 0 < ‖1 - NlsGge.ThirdConsultation.KSPSWKB.beta φ ξ 0 * NlsGge.ThirdConsultation.KSPSWKB.alpha φ ξ 0‖ := by linarith
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  have heq := disc_eventuallyEq_U φ B₀ hφ h13 h14 (show T < ‖ξ‖ by linarith)
  -- derivatives
  obtain ⟨a', hA', ha'⟩ := coeff_deriv_U φ B₀ hφ false ξ hX1
  obtain ⟨b', hB', hb'⟩ := coeff_deriv_U φ B₀ hφ true ξ hX1
  have hA'' : HasDerivAt (fun z : ℂ => NlsGge.ThirdConsultation.KSPSWKB.alpha φ z 0) a' ξ := hA'
  have hB'' : HasDerivAt (fun z : ℂ => NlsGge.ThirdConsultation.KSPSWKB.beta φ z 0) b' ξ := hB'
  have hR : ∀ (b : Bool) (i : Fin 2), HasDerivAt (Rfun φ b i) (deriv (Rfun φ b i) ξ) ξ :=
    fun b i => (Rfun_differentiableAt φ b i hz).hasDerivAt
  have hθ := phaseDerivative_eq_deriv N φ ξ hz
  have hcos := (hθ.ccos).const_mul (2 : ℂ)
  have hDd := (hB''.mul hA'').const_sub (1 : ℂ)
  have hDi := hDd.inv hD
  have hε := hasDerivAt_eps N hz
  have hXd := (((hR false 0).add (hR true 1)).sub (hA''.mul (hR true 0))).sub (hB''.mul (hR false 1))
  have hGd := hcos.add (hDi.mul (hε.mul hXd))
  have hderiv := heq.deriv_eq.trans hGd.deriv
  set r00 : ℂ := Rfun φ false 0 ξ with hr00
  set r11 : ℂ := Rfun φ true 1 ξ with hr11
  set r10 : ℂ := Rfun φ true 0 ξ with hr10
  set r01 : ℂ := Rfun φ false 1 ξ with hr01
  set M : ℂ := -2 * Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * ξ) * integralRiccatiLeft φ (N + 1) with hMdef
  have hw0 : 0 < w := lt_of_lt_of_le one_pos (NlsGge.ThirdConsultation.KSPS015W.one_le_w n)
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  have hmain : NlsGge.ThirdConsultation.KSPSWKB.discriminantDerivativeMain N φ xi n =
      -2 * Complex.sin (wkbPhase φ ξ) * NlsGge.ThirdConsultation.KSPSWKB.phaseDerivative φ ξ +
        ((2 * Complex.I * ξ) ^ N)⁻¹ * M := by
    unfold NlsGge.ThirdConsultation.KSPSWKB.discriminantDerivativeMain
    rw [← hξ, hMdef, zpow_add_one₀ hm1, pow_succ]
    field_simp
  have hα : ‖NlsGge.ThirdConsultation.KSPSWKB.alpha φ ξ 0‖ ≤ S / (2 * X) :=
    NlsGge.ThirdConsultation.KSPSWKB.endpointSum_norm_le B₀ φ hφ false ξ hX1
  have hβ : ‖NlsGge.ThirdConsultation.KSPSWKB.beta φ ξ 0‖ ≤ S / (2 * X) :=
    NlsGge.ThirdConsultation.KSPSWKB.endpointSum_norm_le B₀ φ hφ true ξ hX1
  have hX2 : 0 < X ^ 2 := by positivity
  have ha'' : ‖a'‖ ≤ K / X ^ 2 :=
    ha'.trans (div_le_div_of_nonneg_right (by rw [hKdef]; linarith) hX2.le)
  have hb'' : ‖b'‖ ≤ K / X ^ 2 :=
    hb'.trans (div_le_div_of_nonneg_right (by rw [hKdef]; linarith) hX2.le)
  have hε' : ‖((2 * Complex.I * ξ) ^ N)⁻¹‖ = ((2 * X) ^ N)⁻¹ := by
    rw [norm_inv, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  have hSw : S / (2 * X) ≤ S / w := div_le_div_of_nonneg_left hS0 hw0 hwX
  have hx : ‖r00 + r11 - NlsGge.ThirdConsultation.KSPSWKB.alpha φ ξ 0 * r10 - NlsGge.ThirdConsultation.KSPSWKB.beta φ ξ 0 * r01‖ ≤
      (Pc + S * (U + V)) / w := by
    have k1 : ‖NlsGge.ThirdConsultation.KSPSWKB.alpha φ ξ 0 * r10‖ ≤ S / w * U := by
      rw [norm_mul]; exact mul_le_mul (hα.trans hSw) hu (norm_nonneg _) (by positivity)
    have k2 : ‖NlsGge.ThirdConsultation.KSPSWKB.beta φ ξ 0 * r01‖ ≤ S / w * V := by
      rw [norm_mul]; exact mul_le_mul (hβ.trans hSw) hv (norm_nonneg _) (by positivity)
    have k3 := norm_sub_le (r00 + r11 - NlsGge.ThirdConsultation.KSPSWKB.alpha φ ξ 0 * r10) (NlsGge.ThirdConsultation.KSPSWKB.beta φ ξ 0 * r01)
    have k4 := norm_sub_le (r00 + r11) (NlsGge.ThirdConsultation.KSPSWKB.alpha φ ξ 0 * r10)
    have k5 : (Pc + S * (U + V)) / w = Pc / w + S / w * U + S / w * V := by
      field_simp; ring
    rw [k5]
    linarith
  have hI0 : 0 ≤ CI := (norm_nonneg _).trans hCI
  have hM : ‖M‖ ≤ CI / X := by
    have : ‖M‖ = ‖integralRiccatiLeft φ (N + 1)‖ / X := by
      rw [hMdef, norm_mul, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I,
        norm_zpow, norm_neg, norm_one, one_zpow, Complex.norm_ofNat, ← hXdef]
      field_simp
    rw [this]
    exact div_le_div_of_nonneg_right hCI hX0.le
  have hU0 : 0 ≤ U := le_trans (norm_nonneg _) hu
  have hV0 : 0 ≤ V := le_trans (norm_nonneg _) hv
  have hPn : 0 ≤ Pc + S * (U + V) := by positivity
  exact pure_bound N w X S K (Pc + S * (U + V)) U V FU FL G CI
    ξ (1 - NlsGge.ThirdConsultation.KSPSWKB.beta φ ξ 0 * NlsGge.ThirdConsultation.KSPSWKB.alpha φ ξ 0) (NlsGge.ThirdConsultation.KSPSWKB.alpha φ ξ 0) (NlsGge.ThirdConsultation.KSPSWKB.beta φ ξ 0) a' b'
    ((2 * Complex.I * ξ) ^ N)⁻¹ (r00 + r11 - NlsGge.ThirdConsultation.KSPSWKB.alpha φ ξ 0 * r10 - NlsGge.ThirdConsultation.KSPSWKB.beta φ ξ 0 * r01)
    r10 r01 (deriv (Rfun φ true 0) ξ) (deriv (Rfun φ false 1) ξ)
    (deriv (Rfun φ false 0) ξ + deriv (Rfun φ true 1) ξ) M
    (deriv (discriminant φ) ξ - NlsGge.ThirdConsultation.KSPSWKB.discriminantDerivativeMain N φ xi n)
    hw0 hX1 hwX hS0 hK0 hPn hU0 hV0 ((norm_nonneg _).trans hp10) ((norm_nonneg _).trans hp01)
    hG hI0 rfl rfl hD hDinv hα hβ ha'' hb'' hε' hx hu hv hp10 hp01 hM hpp
    (by rw [hderiv, hmain]; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.inv_apply, hr00, hr11,
      hr10, hr01]; ring)

theorem final_pure (Cst S a1 a2 a3 a4 a5 a6 a7 a8 CI w a10 a11 : ℝ) (hC : 0 ≤ Cst) (hS : 0 ≤ S)
    (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3) (h4 : 0 ≤ a4) (h5 : 0 ≤ a5) (h6 : 0 ≤ a6) (h7 : 0 ≤ a7)
    (h8 : 0 ≤ a8) (hCI : 0 ≤ CI) (hw : 0 < w) (h10 : 0 ≤ a10) (h11 : 0 ≤ a11) :
    Cst * ((a1 + a2 + S * (a3 + a4 + (a5 + a6))) + (a3 + a4) + (a5 + a6) + a7 + a8 + CI / w + (a10 + a11)) ≤
      Cst * (1 + S) * (a1 + (a2 + (a3 + (a4 + (a5 + (a6 + (a7 + (a8 + (CI * (1 / w) + (a10 + a11)))))))))) := by
  have e : Cst * (1 + S) * (a1 + (a2 + (a3 + (a4 + (a5 + (a6 + (a7 + (a8 + (CI * (1 / w) + (a10 + a11)))))))))) -
      Cst * ((a1 + a2 + S * (a3 + a4 + (a5 + a6))) + (a3 + a4) + (a5 + a6) + a7 + a8 + CI / w + (a10 + a11)) =
      Cst * S * (a1 + a2 + a7 + a8 + CI / w + a10 + a11) := by ring
  have : 0 ≤ Cst * S * (a1 + a2 + a7 + a8 + CI / w + a10 + a11) := by positivity
  linarith

/-- The per-index bound of the assembly (one tail index, all constants B₀-uniform). -/
theorem index_bound (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (a : ℝ) (ha : 0 ≤ a) (φ : SobolevC N)
    (hφ : sobolevNorm N φ ≤ B₀)
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (h14 : ∀ lam : {z : ℂ // z ≠ 0}, WKBThreshold N B₀ lam.1 →
      monodromyPair (toPotPair φ) lam.1 = NlsGge.ThirdConsultation.KSPSWKB.explicitWKBMonodromy N φ lam)
    (CI : ℝ) (hIL : ‖integralRiccatiLeft φ (N + 1)‖ ≤ CI)
    (S K1 Cst : ℝ)
    (hS : S = ∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k)
    (hK1 : K1 = ∑ k ∈ Finset.Icc 1 N, (k : ℝ) *
      NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k)
    (hCst : Cst = 4 * (2 * K1) * S + 2 * N + 4 * (2 * K1) + 2 * S + 2 * S ^ 2 + 1)
    (hS0 : 0 ≤ S) (hCst0 : 0 ≤ Cst)
    (xi : ℤ → ℂ) (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (n : ℤ) (hn : ((⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀ + 1⌉₊ + 1 : ℕ) : ℤ) ≤ |n|) :
    indexWeight n ^ (N + 1) *
        ‖deriv (discriminant φ) (xi n) - NlsGge.ThirdConsultation.KSPSWKB.discriminantDerivativeMain N φ xi n‖ ≤
      Cst * (1 + S) * ((‖(indexWeight n : ℂ) * (endpointDiagonalLower N φ xi n -
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1))‖) +
        ((‖(indexWeight n : ℂ) * (endpointDiagonalUpper N φ xi n -
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1))‖) +
        ((‖physicalFourier (iteratedDerivative N φ.1) (-n)‖) +
        ((‖(indexWeight n : ℂ) *
        ((if hz : xi n = 0 then 0 else
            sourceRemainderVector φ true ⟨xi n, hz⟩ 1 (if true then 0 else 1)) -
          (if true then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
            (if true then (-1 : ℂ) ^ (N + 1) else -1) *
            physicalFourier (iteratedDerivative N (if true then φ.1 else φ.2))
              ((if true then (-1 : ℤ) else 1) * n))‖) +
        ((‖physicalFourier (iteratedDerivative N φ.2) n‖) +
        ((‖(indexWeight n : ℂ) *
        ((if hz : xi n = 0 then 0 else
            sourceRemainderVector φ false ⟨xi n, hz⟩ 1 (if false then 0 else 1)) -
          (if false then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
            (if false then (-1 : ℂ) ^ (N + 1) else -1) *
            physicalFourier (iteratedDerivative N (if false then φ.1 else φ.2))
              ((if false then (-1 : ℤ) else 1) * n))‖) +
        ((‖deriv (Rfun φ true 0) (xi n)‖) +
        ((‖deriv (Rfun φ false 1) (xi n)‖) +
        ((CI * (1 / indexWeight n)) +
        ((indexWeight n * ‖deriv (Rfun φ false 0) (xi n) -
        -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1)‖) +
        ((indexWeight n * ‖deriv (Rfun φ true 1) (xi n) -
        -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1)‖)))))))))))) := by
  obtain ⟨hX1, hXT, hwX⟩ := NlsGge.ThirdConsultation.KSPS015W.tail_facts a (NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀ + 1) ha xi hxi n hn
  have hw1 := NlsGge.ThirdConsultation.KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  have hwc : (indexWeight n : ℂ) ≠ 0 := by exact_mod_cast hw0.ne'
  have hz : xi n ≠ 0 := by intro h; rw [h, norm_zero] at hX1; norm_num at hX1
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  -- named per-index quantities
  set tC1 := ‖(indexWeight n : ℂ) * (endpointDiagonalLower N φ xi n -
        (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1))‖ with htC1
  set tC2 := ‖(indexWeight n : ℂ) * (endpointDiagonalUpper N φ xi n -
        (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1))‖ with htC2
  set tF1 := ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ with htF1
  set tF2 := ‖physicalFourier (iteratedDerivative N φ.2) n‖ with htF2
  set tG1 := indexWeight n * ‖deriv (Rfun φ false 0) (xi n) -
      -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1)‖ with htG1
  set tG2 := indexWeight n * ‖deriv (Rfun φ true 1) (xi n) -
      -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1)‖ with htG2
  set tEU := ‖(indexWeight n : ℂ) *
      ((if hz : xi n = 0 then 0 else
          sourceRemainderVector φ true ⟨xi n, hz⟩ 1 (if true then 0 else 1)) -
        (if true then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
          (if true then (-1 : ℂ) ^ (N + 1) else -1) *
          physicalFourier (iteratedDerivative N (if true then φ.1 else φ.2))
            ((if true then (-1 : ℤ) else 1) * n))‖ with htEU
  set tEL := ‖(indexWeight n : ℂ) *
      ((if hz : xi n = 0 then 0 else
          sourceRemainderVector φ false ⟨xi n, hz⟩ 1 (if false then 0 else 1)) -
        (if false then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
          (if false then (-1 : ℂ) ^ (N + 1) else -1) *
          physicalFourier (iteratedDerivative N (if false then φ.1 else φ.2))
            ((if false then (-1 : ℤ) else 1) * n))‖ with htEL
  have hdivle : ∀ e x : ℂ, ‖(indexWeight n : ℂ) * (x - e)‖ = indexWeight n * ‖x - e‖ := by
    intro e x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0.le]
  have hsplit : ∀ x e : ℂ, ‖x‖ ≤ ‖e‖ + ‖(indexWeight n : ℂ) * (x - e)‖ := by
    intro x e
    rw [hdivle]
    have h1 : ‖x‖ ≤ ‖e‖ + ‖x - e‖ := by
      have := norm_add_le e (x - e); rwa [add_sub_cancel] at this
    have h2 : ‖x - e‖ ≤ indexWeight n * ‖x - e‖ := le_mul_of_one_le_left (norm_nonneg _) hw1
    linarith
  have hu : ‖Rfun φ true 0 (xi n)‖ ≤ tF1 + tEU := by
    have e1 : Rfun φ true 0 (xi n) = (if hz : xi n = 0 then 0 else
          sourceRemainderVector φ true ⟨xi n, hz⟩ 1 (if true then 0 else 1)) := rfl
    have e2 : ‖(if true then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
          (if true then (-1 : ℂ) ^ (N + 1) else -1) *
          physicalFourier (iteratedDerivative N (if true then φ.1 else φ.2))
            ((if true then (-1 : ℤ) else 1) * n)‖ = tF1 := by
      simp only [↓reduceIte, htF1, norm_mul, norm_neg, Complex.norm_I, norm_zpow, norm_pow, norm_one, one_zpow,
        one_pow, one_mul, neg_one_mul]
    rw [e1, ← e2]
    exact hsplit _ _
  have hv : ‖Rfun φ false 1 (xi n)‖ ≤ tF2 + tEL := by
    have e1 : Rfun φ false 1 (xi n) = (if hz : xi n = 0 then 0 else
          sourceRemainderVector φ false ⟨xi n, hz⟩ 1 (if false then 0 else 1)) := rfl
    have e2 : ‖(if false then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
          (if false then (-1 : ℂ) ^ (N + 1) else -1) *
          physicalFourier (iteratedDerivative N (if false then φ.1 else φ.2))
            ((if false then (-1 : ℤ) else 1) * n)‖ = tF2 := by
      simp only [Bool.false_eq_true, ↓reduceIte, htF2, norm_mul, norm_neg, Complex.norm_I, norm_zpow,
        norm_one, one_zpow, one_mul]
    rw [e1, ← e2]
    exact hsplit _ _
  have hs : ‖Rfun φ false 0 (xi n) + Rfun φ true 1 (xi n)‖ ≤ (tC1 + tC2) / indexWeight n := by
    have e0 : Rfun φ false 0 (xi n) = endpointDiagonalLower N φ xi n := rfl
    have e1 : Rfun φ true 1 (xi n) = endpointDiagonalUpper N φ xi n := rfl
    have hlead : (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1) +
        (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1) = 0 := by
      rw [← h13 (N + 1) ⟨by omega, le_rfl⟩, zpow_add_one₀ hm1]; ring
    have e : Rfun φ false 0 (xi n) + Rfun φ true 1 (xi n) =
        ((indexWeight n : ℂ) * (endpointDiagonalLower N φ xi n -
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1)) +
        (indexWeight n : ℂ) * (endpointDiagonalUpper N φ xi n -
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1))) /
          (indexWeight n : ℂ) := by
      rw [e0, e1]
      rw [show (indexWeight n : ℂ) * (endpointDiagonalLower N φ xi n -
            (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1)) +
          (indexWeight n : ℂ) * (endpointDiagonalUpper N φ xi n -
            (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1)) =
          (indexWeight n : ℂ) * ((endpointDiagonalLower N φ xi n + endpointDiagonalUpper N φ xi n) -
            ((-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1) +
            (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1))) by ring,
        hlead, sub_zero, mul_div_cancel_left₀ _ hwc]
    rw [e, norm_div, Complex.norm_real, Real.norm_of_nonneg hw0.le]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) hw0.le
  have hpp : ‖deriv (Rfun φ false 0) (xi n) + deriv (Rfun φ true 1) (xi n) -
      -2 * Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1)‖ ≤
        (tG1 + tG2) / indexWeight n := by
    have e : deriv (Rfun φ false 0) (xi n) + deriv (Rfun φ true 1) (xi n) -
        -2 * Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1) =
        (deriv (Rfun φ false 0) (xi n) -
          -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1)) +
        (deriv (Rfun φ true 1) (xi n) -
          -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1)) := by
      rw [← h13 (N + 1) ⟨by omega, le_rfl⟩]; ring
    rw [e]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [htG1, htG2]
    field_simp
  have hPc : 0 ≤ tC1 + tC2 := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hG : 0 ≤ tG1 + tG2 :=
    add_nonneg (mul_nonneg hw0.le (norm_nonneg _)) (mul_nonneg hw0.le (norm_nonneg _))
  have key := pointwise_U N hN B₀ φ hφ h13 h14 xi n hX1 hXT hwX CI hIL (tC1 + tC2) (tF1 + tEU)
    (tF2 + tEL) ‖deriv (Rfun φ true 0) (xi n)‖ ‖deriv (Rfun φ false 1) (xi n)‖ (tG1 + tG2) hPc hG
    hu hv hs hpp le_rfl le_rfl
  rw [← hK1, ← hS, ← hCst] at key
  refine key.trans ?_
  have hI0 : 0 ≤ CI := (norm_nonneg _).trans hIL
  exact final_pure Cst S _ _ _ _ _ _ _ _ CI (indexWeight n) _ _ hCst0 hS0 (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hI0 hw0
    (by positivity) (by positivity)

/-- Ball-uniform tail KSPS-017 assembly (all constants before φ, ξ, F). -/
theorem deriv_tail_of (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (a : ℝ) (ha : 0 ≤ a)
    (h13 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (h14 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ lam : {z : ℂ // z ≠ 0}, WKBThreshold N B₀ lam.1 →
      monodromyPair (toPotPair φ) lam.1 = NlsGge.ThirdConsultation.KSPSWKB.explicitWKBMonodromy N φ lam)
    (CI : ℝ) (hI : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ‖integralRiccatiLeft φ (N + 1)‖ ≤ CI)
    (NL : ℕ) (CL : ℝ)
    (hL : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (NL : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        ((if hz : xi n = 0 then 0 else
            sourceRemainderVector φ false ⟨xi n, hz⟩ 1 (if false then 0 else 1)) -
          (if false then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
            (if false then (-1 : ℂ) ^ (N + 1) else -1) *
            physicalFourier (iteratedDerivative N (if false then φ.1 else φ.2))
              ((if false then (-1 : ℤ) else 1) * n))‖ ^ 2 ≤ CL)
    (NU : ℕ) (CU : ℝ)
    (hU : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (NU : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        ((if hz : xi n = 0 then 0 else
            sourceRemainderVector φ true ⟨xi n, hz⟩ 1 (if true then 0 else 1)) -
          (if true then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
            (if true then (-1 : ℂ) ^ (N + 1) else -1) *
            physicalFourier (iteratedDerivative N (if true then φ.1 else φ.2))
              ((if true then (-1 : ℤ) else 1) * n))‖ ^ 2 ≤ CU)
    (N1 : ℕ) (C1 : ℝ)
    (h1 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (N1 : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        (endpointDiagonalLower N φ xi n -
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1))‖ ^ 2 ≤ C1)
    (N2 : ℕ) (C2 : ℝ)
    (h2 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (N2 : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        (endpointDiagonalUpper N φ xi n -
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1))‖ ^ 2 ≤ C2)
    (ND1 : ℕ) (CD1 : ℝ)
    (hD1 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (ND1 : ℤ) ≤ |n|) →
      ∑ n ∈ F, (indexWeight n * ‖deriv (Rfun φ false 0) (xi n) -
        -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1)‖) ^ 2 ≤ CD1)
    (ND2 : ℕ) (CD2 : ℝ)
    (hD2 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (ND2 : ℤ) ≤ |n|) →
      ∑ n ∈ F, (indexWeight n * ‖deriv (Rfun φ true 1) (xi n) -
        -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1)‖) ^ 2 ≤ CD2)
    (NO1 : ℕ) (CO1 : ℝ)
    (hO1 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (NO1 : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖deriv (Rfun φ true 0) (xi n)‖ ^ 2 ≤ CO1)
    (NO2 : ℕ) (CO2 : ℝ)
    (hO2 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (NO2 : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖deriv (Rfun φ false 1) (xi n)‖ ^ 2 ≤ CO2) :
    ∃ (M : ℕ) (C : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) *
          ‖deriv (discriminant φ) (xi n) - NlsGge.ThirdConsultation.KSPSWKB.discriminantDerivativeMain N φ xi n‖) ^ 2 ≤ C := by
  set S : ℝ := ∑ k ∈ Finset.Icc 1 N,
    NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun k hk => NlsGge.ThirdConsultation.KSPSWKB.endpointCoefficientBound_nonneg N B₀ k hk)
  set K1 : ℝ := ∑ k ∈ Finset.Icc 1 N, (k : ℝ) *
    NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k with hK1def
  have hK10 : 0 ≤ K1 := Finset.sum_nonneg (fun k hk =>
    mul_nonneg (Nat.cast_nonneg k) (NlsGge.ThirdConsultation.KSPSWKB.endpointCoefficientBound_nonneg N B₀ k hk))
  set Cst : ℝ := 4 * (2 * K1) * S + 2 * N + 4 * (2 * K1) + 2 * S + 2 * S ^ 2 + 1 with hCst
  have hCst0 : 0 ≤ Cst := by positivity
  set Km : ℝ := Cst * (1 + S) with hKm
  have hKm0 : 0 ≤ Km := by positivity
  set T : ℝ := NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀ with hTdef
  set P2 : ℝ := ((2 * Real.pi) ^ N) ^ 2 * B₀ ^ 2 with hP2
  set Sv : ℝ := ∑' n : ℤ, (1 / indexWeight n) ^ 2 with hSv
  set M : ℕ := max (max (max (max NL NU) (max N1 N2)) (max (max ND1 ND2) (max NO1 NO2)))
    (⌈a⌉₊ + ⌈T + 1⌉₊ + 1) with hMdef
  refine ⟨M, Km ^ 2 * (((11 : ℕ) : ℝ) * (C1 + C2 + P2 + CU + P2 + CL + CO1 + CO2 + CI ^ 2 * Sv + CD1 + CD2)),
    fun φ hφ xi hxi F hF => ?_⟩
  have hle : ∀ (j : ℕ), j ≤ M → ∀ n ∈ F, (j : ℤ) ≤ |n| := fun j hj n hn =>
    le_trans (Nat.cast_le.mpr hj) (hF n hn)
  have hFL := hle NL (by omega)
  have hFU := hle NU (by omega)
  have hF1 := hle N1 (by omega)
  have hF2 := hle N2 (by omega)
  have hFD1 := hle ND1 (by omega)
  have hFD2 := hle ND2 (by omega)
  have hFO1 := hle NO1 (by omega)
  have hFO2 := hle NO2 (by omega)
  have hFT := hle (⌈a⌉₊ + ⌈T + 1⌉₊ + 1) (by omega)
  have hF1abs : ∀ n ∈ F, 1 ≤ |(n : ℝ)| := by
    intro n hn
    have h := hFT n hn
    have h' : (1 : ℤ) ≤ |n| := le_trans (by omega) h
    have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.2 h'
    rw [Int.cast_abs] at this; simpa using this
  obtain ⟨hFour1, hFour2⟩ := fourier_iter_sums_le φ hφ F hF1abs
  have hIL := hI φ hφ
  have hrel := h13 φ hφ
  refine NlsGge.ThirdConsultation.KSPS017U0.sum_sq_le_fin F _
    ![fun n => ‖(indexWeight n : ℂ) * (endpointDiagonalLower N φ xi n -
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1))‖,
      fun n => ‖(indexWeight n : ℂ) * (endpointDiagonalUpper N φ xi n -
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1))‖,
      fun n => ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖,
      fun n => ‖(indexWeight n : ℂ) *
        ((if hz : xi n = 0 then 0 else
            sourceRemainderVector φ true ⟨xi n, hz⟩ 1 (if true then 0 else 1)) -
          (if true then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
            (if true then (-1 : ℂ) ^ (N + 1) else -1) *
            physicalFourier (iteratedDerivative N (if true then φ.1 else φ.2))
              ((if true then (-1 : ℤ) else 1) * n))‖,
      fun n => ‖physicalFourier (iteratedDerivative N φ.2) n‖,
      fun n => ‖(indexWeight n : ℂ) *
        ((if hz : xi n = 0 then 0 else
            sourceRemainderVector φ false ⟨xi n, hz⟩ 1 (if false then 0 else 1)) -
          (if false then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
            (if false then (-1 : ℂ) ^ (N + 1) else -1) *
            physicalFourier (iteratedDerivative N (if false then φ.1 else φ.2))
              ((if false then (-1 : ℤ) else 1) * n))‖,
      fun n => ‖deriv (Rfun φ true 0) (xi n)‖,
      fun n => ‖deriv (Rfun φ false 1) (xi n)‖,
      fun n => CI * (1 / indexWeight n),
      fun n => indexWeight n * ‖deriv (Rfun φ false 0) (xi n) -
        -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1)‖,
      fun n => indexWeight n * ‖deriv (Rfun φ true 1) (xi n) -
        -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1)‖]
    Km hKm0 ?_ ![C1, C2, P2, CU, P2, CL, CO1, CO2, CI ^ 2 * Sv, CD1, CD2] ?_ |>.trans (le_of_eq ?_)
  · intro n hn
    refine ⟨mul_nonneg (pow_nonneg (le_trans zero_le_one (NlsGge.ThirdConsultation.KSPS015W.one_le_w n)) _) (norm_nonneg _), ?_⟩
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
    exact index_bound N hN B₀ a ha φ hφ hrel (h14 φ hφ) CI hIL S K1 Cst hSdef hK1def hCst hS0 hCst0 xi hxi n
      (hFT n hn)
  · intro j
    fin_cases j
    · exact h1 φ hφ xi hxi F hF1
    · exact h2 φ hφ xi hxi F hF2
    · exact hFour1
    · exact hU φ hφ xi hxi F hFU
    · exact hFour2
    · exact hL φ hφ xi hxi F hFL
    · exact hO1 φ hφ xi hxi F hFO1
    · exact hO2 φ hφ xi hxi F hFO2
    · show ∑ n ∈ F, (CI * (1 / indexWeight n)) ^ 2 ≤ CI ^ 2 * Sv
      rw [show ∑ n ∈ F, (CI * (1 / indexWeight n)) ^ 2 = CI ^ 2 * ∑ n ∈ F, (1 / indexWeight n) ^ 2 by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)]
      exact mul_le_mul_of_nonneg_left (inv_w_sq_summable.sum_le_tsum F (fun n _ => sq_nonneg _)) (sq_nonneg _)
    · exact hD1 φ hφ xi hxi F hFD1
    · exact hD2 φ hφ xi hxi F hFD2
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
    ring

end
end NlsGge.ThirdConsultation.KSPS017U4
