import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Support6
import NlsGge.ThirdConsultation.KSPS.KSPS012Support10
import NlsGge.ThirdConsultation.KSPS.KSPS012Support11
import NlsGge.ThirdConsultation.KSPS.KSPS017Support9
import NlsGge.Atomic.KSPS.KSPS013
import NlsGge.ThirdConsultation.KSPS.KSPS031SharpRL

/- KSPS-031 SHARP ENDPOINTS PRODUCTION02 (proof development, AUTHOR; not reviewed; needs ROOT MAIN PROBE).
   PRODUCTION02 repairs SHARP_MAINPROBE01 errors L709/711 (explicit div_atTop), L887 (pure chart_mul_decomp
   replaces field_simp), L976 (bound the simp-normal form -(I*osc)). Intended target
   NlsGge/ThirdConsultation/KSPS/KSPS031SharpEndpoints.lean, module …KSPS.KSPS031SharpEndpoints.
   Pro round 16 §2.2–§2.3 along an arbitrary real frequency sequence ω_j → ∞ (later ω_j = (j+1/2)π):
   * diagonal endpoints KEEP their phases:
       2iω R00 − e^{−iω} I → 0,   2iω R11 + e^{iω} I → 0,   I = integralRiccatiLeft φ (N+1),
     from diag_approx_false/true (error O(|ω|^{-2})), the exact IBP KSPS012Support6.core_decomp,
     KSPS012Support11.integralRiccatiLeft_eq / integralRiccatiRight_eq, KSPS-013 (right = left), and the
     Riemann–Lebesgue / dominated-convergence decay KSPS031SharpRL.osc_tendsto / tz_tendsto;
   * off-diagonal endpoints → 0 from KSPS017W.off_approx and osc_tendsto.
   Recorded variant: decay (→ 0) instead of Pro's ℓ² Bessel estimates; sufficient for the little-o head. -/
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section

theorem norm_exp_neg_I_real (x : ℝ) : ‖Complex.exp (-(Complex.I * (x : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * (x : ℂ)) = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem norm_exp_I_real (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I by ring, Complex.norm_exp_ofReal_mul_I]

theorem neg_tendsto_cobounded {ω : ℤ → ℝ} (hω : Tendsto ω cofinite (Bornology.cobounded ℝ)) :
    Tendsto (fun j => -ω j) cofinite (Bornology.cobounded ℝ) := by
  have h := (NlsGge.ThirdConsultation.KSPS031SharpRL.tendsto_scale_cobounded
    (r := -1) (by norm_num)).comp hω
  refine h.congr (fun j => ?_)
  simp only [Function.comp_apply]
  ring

theorem inv_norm_tendsto {ω : ℤ → ℝ} (hω : Tendsto ω cofinite (Bornology.cobounded ℝ)) (C : ℝ) :
    Tendsto (fun j => C / ‖((ω j : ℝ) : ℂ)‖) cofinite (𝓝 0) := by
  have h : Tendsto (fun j => ‖ω j‖) cofinite atTop := tendsto_norm_atTop_iff_cobounded.2 hω
  have h2 : Tendsto (fun j : ℤ => C / ‖ω j‖) cofinite (𝓝 0) :=
    Filter.Tendsto.div_atTop (tendsto_const_nhds (x := C)) h
  refine h2.congr (fun j => ?_)
  rw [Complex.norm_real]

/-- Pure algebra used after `core_decomp`: multiply its right side by ν = 2iμ. -/
theorem chart_mul_decomp (ν pv O e P T : ℂ) (hν : ν ≠ 0) :
    ν * (-(pv / ν) * O + e / ν * (P + T)) = -pv * O + e * (P + T) := by
  field_simp

/-- Lower diagonal endpoint with its phase retained. -/
theorem diag_lower_phase_tendsto {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (ω : ℤ → ℝ)
    (hω : Tendsto ω cofinite (Bornology.cobounded ℝ)) (hne : ∀ j, ((ω j : ℝ) : ℂ) ≠ 0) :
    Tendsto (fun j => 2 * Complex.I * ((ω j : ℝ) : ℂ) *
        sourceRemainderVector φ false ⟨(ω j : ℂ), hne j⟩ 1 0 -
        Complex.exp (-(Complex.I * ((ω j : ℝ) : ℂ))) * integralRiccatiLeft φ (N + 1))
      cofinite (𝓝 0) := by
  obtain ⟨φ', hφ'⟩ := NlsGge.ThirdConsultation.KSPS011Support4.exists_toPair_eq hN φ
  obtain ⟨D, L, hD, hL, hap⟩ := diag_approx_false hN φ φ' hφ' 0 le_rfl
  have hu : coverRep38 (physicalSobolevEmbed 1 φ'.1) = coverRep38 (toPotPair φ).1 := by
    rw [← hφ']; rfl
  have hP : integralRiccatiLeft φ (N + 1) = ∫ t in (0 : ℝ)..1,
      coverRep38 (physicalSobolevEmbed 1 φ'.1) t *
        coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t := by
    rw [integralRiccatiLeft_eq, hu]
  have hci := intervalIntegrable_coverRep38_one
    (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1))
  have hdi := intervalIntegrable_coverRep38_one (physicalSobolevDerivative38 1 φ'.1)
  have hosc := (NlsGge.ThirdConsultation.KSPS031SharpRL.osc_tendsto
    (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)))).comp hω
  have htz := (NlsGge.ThirdConsultation.KSPS031SharpRL.tz_tendsto
    (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)))
    (coverRep38 (physicalSobolevDerivative38 1 φ'.1)) hci hdi).comp hω
  have hg : Tendsto (fun j => 2 * D / ‖((ω j : ℝ) : ℂ)‖ +
      ‖sobolevPointValue 1 φ'.1 1‖ * ‖endpointOsc ((ω j : ℝ) : ℂ)
        (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)))‖ +
      ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz
        (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)))
        (coverRep38 (physicalSobolevDerivative38 1 φ'.1)) ((ω j : ℝ) : ℂ)‖) cofinite (𝓝 0) := by
    have t1 := inv_norm_tendsto hω (2 * D)
    have t2 := (hosc.norm).const_mul ‖sobolevPointValue 1 φ'.1 1‖
    have t3 := htz.norm
    rw [norm_zero, mul_zero] at t2
    rw [norm_zero] at t3
    have := (t1.add t2).add t3
    rw [add_zero, add_zero] at this
    exact this
  have hbig : ∀ᶠ j in cofinite, L ≤ ‖((ω j : ℝ) : ℂ)‖ := by
    have h : Tendsto (fun j => ‖ω j‖) cofinite atTop := tendsto_norm_atTop_iff_cobounded.2 hω
    filter_upwards [(tendsto_atTop.1 h) L] with j hj
    rwa [Complex.norm_real]
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [hbig] with j hj
  set μ : ℂ := ((ω j : ℝ) : ℂ) with hμ
  have hμ0 : μ ≠ 0 := hne j
  have hz1 : 1 ≤ ‖μ‖ := hL.trans hj
  have hzpos : 0 < ‖μ‖ := by linarith
  have him : |μ.im| ≤ 0 := by rw [hμ, Complex.ofReal_im, abs_zero]
  have happ := hap ⟨μ, hμ0⟩ hj him
  dsimp only at happ
  have hdec := core_decomp φ'.1 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) hμ0
  set X := -Complex.exp (-(2 * Complex.I * μ)) * endpointOsc μ (fun t =>
      (∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) *
        coverRep38 (physicalSobolevEmbed 1 φ'.1) s) *
      coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t) with hX
  set R := sourceRemainderVector φ false ⟨μ, hμ0⟩ 1 0 with hR
  set O := endpointOsc μ
    (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1))) with hO
  set T := NlsGge.ThirdConsultation.KSPS012Support5.Tz
    (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)))
    (coverRep38 (physicalSobolevDerivative38 1 φ'.1)) μ with hT
  set pv := sobolevPointValue 1 φ'.1 1 with hpv
  rw [hP]
  set P := ∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 φ'.1) t *
      coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t with hPdef
  have hν : 2 * Complex.I * μ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hμ0
  have hdec' : 2 * Complex.I * μ * X = -pv * O + Complex.exp (-(Complex.I * μ)) * (P + T) := by
    rw [hdec]
    exact chart_mul_decomp _ _ _ _ _ _ hν
  have key : 2 * Complex.I * μ * R - Complex.exp (-(Complex.I * μ)) * P =
      2 * Complex.I * μ * (R - X) - pv * O + Complex.exp (-(Complex.I * μ)) * T := by
    linear_combination hdec'
  rw [key]
  have hRX : ‖R - X‖ ≤ D / ‖μ‖ ^ 2 := happ
  have hνn : ‖2 * Complex.I * μ‖ = 2 * ‖μ‖ := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
  have h1 : ‖2 * Complex.I * μ * (R - X)‖ ≤ 2 * D / ‖μ‖ := by
    rw [norm_mul, hνn]
    calc 2 * ‖μ‖ * ‖R - X‖ ≤ 2 * ‖μ‖ * (D / ‖μ‖ ^ 2) := by gcongr
      _ = 2 * D / ‖μ‖ := by field_simp
  have h3 : ‖Complex.exp (-(Complex.I * μ)) * T‖ = ‖T‖ := by
    rw [norm_mul, hμ, norm_exp_neg_I_real, one_mul]
  calc ‖2 * Complex.I * μ * (R - X) - pv * O + Complex.exp (-(Complex.I * μ)) * T‖
      ≤ ‖2 * Complex.I * μ * (R - X)‖ + ‖pv * O‖ + ‖Complex.exp (-(Complex.I * μ)) * T‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ 2 * D / ‖μ‖ + ‖pv‖ * ‖O‖ + ‖T‖ := by
        rw [norm_mul (pv) O, h3]
        linarith

/-- Upper diagonal endpoint with its phase retained. -/
theorem diag_upper_phase_tendsto {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (ω : ℤ → ℝ)
    (hω : Tendsto ω cofinite (Bornology.cobounded ℝ)) (hne : ∀ j, ((ω j : ℝ) : ℂ) ≠ 0) :
    Tendsto (fun j => 2 * Complex.I * ((ω j : ℝ) : ℂ) *
        sourceRemainderVector φ true ⟨(ω j : ℂ), hne j⟩ 1 1 +
        Complex.exp (Complex.I * ((ω j : ℝ) : ℂ)) * integralRiccatiLeft φ (N + 1))
      cofinite (𝓝 0) := by
  obtain ⟨φ', hφ'⟩ := NlsGge.ThirdConsultation.KSPS011Support4.exists_toPair_eq hN φ
  obtain ⟨D, L, hD, hL, hap⟩ := diag_approx_true hN φ φ' hφ' 0 le_rfl
  have hu : coverRep38 (physicalSobolevEmbed 1 φ'.2) = coverRep38 (toPotPair φ).2 := by
    rw [← hφ']; rfl
  have hP : integralRiccatiLeft φ (N + 1) = ∫ t in (0 : ℝ)..1,
      coverRep38 (physicalSobolevEmbed 1 φ'.2) t *
        coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t := by
    rw [integrated_riccati_vanishing N (N + 1) φ ⟨by omega, le_rfl⟩, integralRiccatiRight_eq, hu]
  have hci := intervalIntegrable_coverRep38_one
    (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1))
  have hdi := intervalIntegrable_coverRep38_one (physicalSobolevDerivative38 1 φ'.2)
  have hω' := neg_tendsto_cobounded hω
  have hosc := (NlsGge.ThirdConsultation.KSPS031SharpRL.osc_tendsto
    (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)))).comp hω'
  have htz := (NlsGge.ThirdConsultation.KSPS031SharpRL.tz_tendsto
    (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)))
    (coverRep38 (physicalSobolevDerivative38 1 φ'.2)) hci hdi).comp hω'
  have hosc' : Tendsto (fun j => endpointOsc (-((ω j : ℝ) : ℂ))
      (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1))))
      cofinite (𝓝 0) := by
    refine hosc.congr (fun j => ?_)
    simp only [Function.comp_apply, Complex.ofReal_neg]
    rfl
  have htz' : Tendsto (fun j => NlsGge.ThirdConsultation.KSPS012Support5.Tz
      (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)))
      (coverRep38 (physicalSobolevDerivative38 1 φ'.2)) (-((ω j : ℝ) : ℂ))) cofinite (𝓝 0) := by
    refine htz.congr (fun j => ?_)
    simp only [Function.comp_apply, Complex.ofReal_neg]
    rfl
  have hg : Tendsto (fun j => 2 * D / ‖((ω j : ℝ) : ℂ)‖ +
      ‖sobolevPointValue 1 φ'.2 1‖ * ‖endpointOsc (-((ω j : ℝ) : ℂ))
        (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)))‖ +
      ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz
        (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)))
        (coverRep38 (physicalSobolevDerivative38 1 φ'.2)) (-((ω j : ℝ) : ℂ))‖) cofinite (𝓝 0) := by
    have t1 := inv_norm_tendsto hω (2 * D)
    have t2 := (hosc'.norm).const_mul ‖sobolevPointValue 1 φ'.2 1‖
    have t3 := htz'.norm
    rw [norm_zero, mul_zero] at t2
    rw [norm_zero] at t3
    have := (t1.add t2).add t3
    rw [add_zero, add_zero] at this
    exact this
  have hbig : ∀ᶠ j in cofinite, L ≤ ‖((ω j : ℝ) : ℂ)‖ := by
    have h : Tendsto (fun j => ‖ω j‖) cofinite atTop := tendsto_norm_atTop_iff_cobounded.2 hω
    filter_upwards [(tendsto_atTop.1 h) L] with j hj
    rwa [Complex.norm_real]
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [hbig] with j hj
  set μ : ℂ := ((ω j : ℝ) : ℂ) with hμ
  have hμ0 : μ ≠ 0 := hne j
  have hμ0' : -μ ≠ 0 := neg_ne_zero.2 hμ0
  have hz1 : 1 ≤ ‖μ‖ := hL.trans hj
  have hzpos : 0 < ‖μ‖ := by linarith
  have him : |μ.im| ≤ 0 := by rw [hμ, Complex.ofReal_im, abs_zero]
  have happ := hap ⟨μ, hμ0⟩ hj him
  dsimp only at happ
  have hdec := core_decomp φ'.2 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) hμ0'
  set X := -Complex.exp (-(2 * Complex.I * (-μ))) * endpointOsc (-μ) (fun t =>
      (∫ s in t..1, Complex.exp (2 * Complex.I * (-μ) * (s : ℂ)) *
        coverRep38 (physicalSobolevEmbed 1 φ'.2) s) *
      coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t) with hX
  set R := sourceRemainderVector φ true ⟨μ, hμ0⟩ 1 1 with hR
  set O := endpointOsc (-μ)
    (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1))) with hO
  set T := NlsGge.ThirdConsultation.KSPS012Support5.Tz
    (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)))
    (coverRep38 (physicalSobolevDerivative38 1 φ'.2)) (-μ) with hT
  set pv := sobolevPointValue 1 φ'.2 1 with hpv
  rw [hP]
  set P := ∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 φ'.2) t *
      coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t with hPdef
  have hν : 2 * Complex.I * (-μ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hμ0'
  have hdec' : 2 * Complex.I * (-μ) * X =
      -pv * O + Complex.exp (-(Complex.I * (-μ))) * (P + T) := by
    rw [hdec]
    exact chart_mul_decomp _ _ _ _ _ _ hν
  have hexp : Complex.exp (-(Complex.I * (-μ))) = Complex.exp (Complex.I * μ) := by
    congr 1; ring
  rw [hexp] at hdec'
  have key : 2 * Complex.I * μ * R + Complex.exp (Complex.I * μ) * P =
      -(2 * Complex.I * (-μ) * (R - X)) + pv * O - Complex.exp (Complex.I * μ) * T := by
    linear_combination (-1 : ℂ) * hdec'
  rw [key]
  have hRX : ‖R - X‖ ≤ D / ‖μ‖ ^ 2 := happ
  have hνn : ‖2 * Complex.I * (-μ)‖ = 2 * ‖μ‖ := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one, norm_neg]
  have h1 : ‖-(2 * Complex.I * (-μ) * (R - X))‖ ≤ 2 * D / ‖μ‖ := by
    rw [norm_neg, norm_mul, hνn]
    calc 2 * ‖μ‖ * ‖R - X‖ ≤ 2 * ‖μ‖ * (D / ‖μ‖ ^ 2) := by gcongr
      _ = 2 * D / ‖μ‖ := by field_simp
  have h3 : ‖Complex.exp (Complex.I * μ) * T‖ = ‖T‖ := by
    rw [norm_mul, hμ, norm_exp_I_real, one_mul]
  calc ‖-(2 * Complex.I * (-μ) * (R - X)) + pv * O - Complex.exp (Complex.I * μ) * T‖
      ≤ ‖-(2 * Complex.I * (-μ) * (R - X))‖ + ‖pv * O‖ + ‖Complex.exp (Complex.I * μ) * T‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 2 * D / ‖μ‖ + ‖pv‖ * ‖O‖ + ‖T‖ := by
        rw [norm_mul pv O, h3]
        linarith

/-- Off-diagonal endpoint (b = false, entry 1) tends to zero along real frequencies. -/
theorem off_lower_tendsto {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (ω : ℤ → ℝ)
    (hω : Tendsto ω cofinite (Bornology.cobounded ℝ)) (hne : ∀ j, ((ω j : ℝ) : ℂ) ≠ 0) :
    Tendsto (fun j => sourceRemainderVector φ false ⟨(ω j : ℂ), hne j⟩ 1 1) cofinite (𝓝 0) := by
  obtain ⟨O, L, hO, hL, hoff⟩ := NlsGge.ThirdConsultation.KSPS017W.off_approx hN φ false 0 le_rfl
  have hosc := (NlsGge.ThirdConsultation.KSPS031SharpRL.osc_tendsto
    (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)))).comp hω
  have hg : Tendsto (fun j => O / ‖((ω j : ℝ) : ℂ)‖ + ‖endpointOsc ((ω j : ℝ) : ℂ)
      (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)))‖)
      cofinite (𝓝 0) := by
    have := (inv_norm_tendsto hω O).add hosc.norm
    rw [norm_zero, add_zero] at this
    exact this
  have hbig : ∀ᶠ j in cofinite, L ≤ ‖((ω j : ℝ) : ℂ)‖ := by
    have h : Tendsto (fun j => ‖ω j‖) cofinite atTop := tendsto_norm_atTop_iff_cobounded.2 hω
    filter_upwards [(tendsto_atTop.1 h) L] with j hj
    rwa [Complex.norm_real]
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [hbig] with j hj
  have him : |(((ω j : ℝ) : ℂ)).im| ≤ 0 := by rw [Complex.ofReal_im, abs_zero]
  have h := hoff ⟨(ω j : ℂ), hne j⟩ hj him
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h
  have htri := norm_sub_norm_le (sourceRemainderVector φ false ⟨(ω j : ℂ), hne j⟩ 1 1)
    (Complex.I * endpointOsc ((ω j : ℝ) : ℂ)
      (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1))))
  rw [norm_mul, Complex.norm_I, one_mul] at htri
  linarith

/-- Off-diagonal endpoint (b = true, entry 0) tends to zero along real frequencies. -/
theorem off_upper_tendsto {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (ω : ℤ → ℝ)
    (hω : Tendsto ω cofinite (Bornology.cobounded ℝ)) (hne : ∀ j, ((ω j : ℝ) : ℂ) ≠ 0) :
    Tendsto (fun j => sourceRemainderVector φ true ⟨(ω j : ℂ), hne j⟩ 1 0) cofinite (𝓝 0) := by
  obtain ⟨O, L, hO, hL, hoff⟩ := NlsGge.ThirdConsultation.KSPS017W.off_approx hN φ true 0 le_rfl
  have hω' := neg_tendsto_cobounded hω
  have hosc := (NlsGge.ThirdConsultation.KSPS031SharpRL.osc_tendsto
    (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)))).comp hω'
  have hosc' : Tendsto (fun j => endpointOsc (-((ω j : ℝ) : ℂ))
      (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1))))
      cofinite (𝓝 0) := by
    refine hosc.congr (fun j => ?_)
    simp only [Function.comp_apply, Complex.ofReal_neg]
    rfl
  have hg : Tendsto (fun j => O / ‖((ω j : ℝ) : ℂ)‖ + ‖endpointOsc (-((ω j : ℝ) : ℂ))
      (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)))‖)
      cofinite (𝓝 0) := by
    have := (inv_norm_tendsto hω O).add hosc'.norm
    rw [norm_zero, add_zero] at this
    exact this
  have hbig : ∀ᶠ j in cofinite, L ≤ ‖((ω j : ℝ) : ℂ)‖ := by
    have h : Tendsto (fun j => ‖ω j‖) cofinite atTop := tendsto_norm_atTop_iff_cobounded.2 hω
    filter_upwards [(tendsto_atTop.1 h) L] with j hj
    rwa [Complex.norm_real]
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [hbig] with j hj
  have him : |(((ω j : ℝ) : ℂ)).im| ≤ 0 := by rw [Complex.ofReal_im, abs_zero]
  have h := hoff ⟨(ω j : ℂ), hne j⟩ hj him
  simp only [↓reduceIte, neg_mul, one_mul] at h
  have htri := (norm_sub_norm_le _ _).trans h
  have hk : ‖-(Complex.I * endpointOsc (-((ω j : ℝ) : ℂ))
      (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1))))‖ =
      ‖endpointOsc (-((ω j : ℝ) : ℂ))
        (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)))‖ := by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
  linarith

end
end NlsGge.ThirdConsultation.KSPSWKB
