import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Support10
import NlsGge.ThirdConsultation.KSPS.KSPS017Support9
import NlsGge.ThirdConsultation.KSPS.KSPS015Support
import NlsGge.Atomic.KSPS.KSPS013
import NlsGge.Atomic.KSPS.KSPS014
import NlsGge.ThirdConsultation.KSPS.KSPS031Analytic

/- KSPS-031 STRIP (proof development, AUTHOR; not reviewed; needs ROOT MAIN PROBE). Intended target
   NlsGge/ThirdConsultation/KSPS/KSPS031Strip.lean, module NlsGge.ThirdConsultation.KSPS.KSPS031Strip.
   Pro round 15 Q4 §1–§2 (PRO_DEFINITION_RESPONSE_FP80_15.md), heads VERBATIM:
   `KSPSWKB.endpoint_remainders_bounded_on_strip` and `KSPS.discriminant_wkb_strip_bound`.
   §1: exists_toPair_eq, q_bound, diag_approx_false/true, norm_endpointOsc_mul_le (diagonal, multiplier q),
       KSPS017W.off_approx with norm_endpointOsc_mul_le at multiplier 1 (off-diagonal); M = max of the four.
   §2: exact KSPS015W.disc_identity with integrated_riccati_vanishing, WKB_monodromy_entries (B = sobolevNorm),
       initialColumns_det_bound, endpointSum_norm_le; scalar estimate KSPS031Analytic.discriminant_error_bound,
       C = 6 M, L = max(L_endpoint, threshold). No hypothesis added. -/
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped BigOperators
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section

/-- Norm of the diagonal principal term: exp prefactor times an oscillatory integral. -/
theorem diag_principal_le {μ : ℂ} {τ Q : ℝ} (hμ : |μ.im| ≤ τ) {q H : ℝ → ℂ}
    (hq : ∀ t ∈ Icc (0 : ℝ) 1, ‖q t‖ ≤ Q) (hH : IntervalIntegrable (fun t => ‖H t‖) volume 0 1) :
    ‖-Complex.exp (-(2 * Complex.I * μ)) * endpointOsc μ (fun t => q t * H t)‖ ≤
      Real.exp (2 * τ) * (Real.exp τ * Q * ∫ t in (0 : ℝ)..1, ‖H t‖) := by
  have hexp : ‖-Complex.exp (-(2 * Complex.I * μ))‖ ≤ Real.exp (2 * τ) := by
    rw [norm_neg, Complex.norm_exp]
    apply Real.exp_le_exp.2
    have h : (-(2 * Complex.I * μ)).re = 2 * μ.im := by simp [Complex.mul_re]
    rw [h]
    have := le_abs_self μ.im
    linarith
  have hosc := norm_endpointOsc_mul_le hμ hq hH
  rw [norm_mul]
  exact mul_le_mul hexp hosc (norm_nonneg _) (Real.exp_pos _).le

theorem diag_false_bounded {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ M L : ℝ, 0 ≤ M ∧ 1 ≤ L ∧ ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ τ →
      ‖sourceRemainderVector φ false lam 1 0‖ ≤ M := by
  obtain ⟨φ', hφ'⟩ := NlsGge.ThirdConsultation.KSPS011Support4.exists_toPair_eq hN φ
  obtain ⟨D, L, hD, hL, hdiag⟩ := diag_approx_false hN φ φ' hφ' τ hτ
  obtain ⟨Q, hQ, hq⟩ := q_bound φ'.1 τ hτ
  have hcii : IntervalIntegrable (fun t => ‖coverRep38
      (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t‖) volume 0 1 :=
    (intervalIntegrable_of_memLp (NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc
      (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)))).norm
  have hCc : 0 ≤ ∫ t in (0 : ℝ)..1, ‖coverRep38
      (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t‖ :=
    intervalIntegral.integral_nonneg zero_le_one (fun t _ => norm_nonneg _)
  refine ⟨D + Real.exp (2 * τ) * (Real.exp τ * Q * ∫ t in (0 : ℝ)..1, ‖coverRep38
      (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t‖), L,
    add_nonneg hD (mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (mul_nonneg (Real.exp_pos _).le hQ) hCc)), hL, fun lam hlam him => ?_⟩
  have hz1 : 1 ≤ ‖lam.1‖ := hL.trans hlam
  have h1 := hdiag lam hlam him
  have htri := (norm_sub_norm_le _ _).trans h1
  have hP := diag_principal_le (μ := lam.1) (τ := τ) (Q := Q / ‖lam.1‖) him
    (q := fun t => ∫ s in t..1, Complex.exp (2 * Complex.I * lam.1 * (s : ℂ)) *
      coverRep38 (physicalSobolevEmbed 1 φ'.1) s)
    (H := coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)))
    (fun t ht => hq lam.1 lam.2 him t ht) hcii
  have hQz : Q / ‖lam.1‖ ≤ Q := div_le_self hQ hz1
  have hDz : D / ‖lam.1‖ ^ 2 ≤ D := div_le_self hD (one_le_pow₀ hz1)
  have hmono : Real.exp (2 * τ) * (Real.exp τ * (Q / ‖lam.1‖) * ∫ t in (0 : ℝ)..1, ‖coverRep38
        (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t‖) ≤
      Real.exp (2 * τ) * (Real.exp τ * Q * ∫ t in (0 : ℝ)..1, ‖coverRep38
        (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t‖) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_right _ hCc
    exact mul_le_mul_of_nonneg_left hQz (Real.exp_pos _).le
  try beta_reduce at hP
  linarith

theorem diag_true_bounded {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ M L : ℝ, 0 ≤ M ∧ 1 ≤ L ∧ ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ τ →
      ‖sourceRemainderVector φ true lam 1 1‖ ≤ M := by
  obtain ⟨φ', hφ'⟩ := NlsGge.ThirdConsultation.KSPS011Support4.exists_toPair_eq hN φ
  obtain ⟨D, L, hD, hL, hdiag⟩ := diag_approx_true hN φ φ' hφ' τ hτ
  obtain ⟨Q, hQ, hq⟩ := q_bound φ'.2 τ hτ
  have hcii : IntervalIntegrable (fun t => ‖coverRep38
      (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t‖) volume 0 1 :=
    (intervalIntegrable_of_memLp (NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc
      (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)))).norm
  have hCc : 0 ≤ ∫ t in (0 : ℝ)..1, ‖coverRep38
      (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t‖ :=
    intervalIntegral.integral_nonneg zero_le_one (fun t _ => norm_nonneg _)
  refine ⟨D + Real.exp (2 * τ) * (Real.exp τ * Q * ∫ t in (0 : ℝ)..1, ‖coverRep38
      (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t‖), L,
    add_nonneg hD (mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (mul_nonneg (Real.exp_pos _).le hQ) hCc)), hL, fun lam hlam him => ?_⟩
  have hz1 : 1 ≤ ‖lam.1‖ := hL.trans hlam
  have him' : |(-lam.1).im| ≤ τ := by simpa using him
  have hne : -lam.1 ≠ 0 := neg_ne_zero.2 lam.2
  have h1 := hdiag lam hlam him
  have htri := (norm_sub_norm_le _ _).trans h1
  have hP := diag_principal_le (μ := -lam.1) (τ := τ) (Q := Q / ‖lam.1‖) him'
    (q := fun t => ∫ s in t..1, Complex.exp (2 * Complex.I * (-lam.1) * (s : ℂ)) *
      coverRep38 (physicalSobolevEmbed 1 φ'.2) s)
    (H := coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)))
    (fun t ht => by simpa [norm_neg] using hq (-lam.1) hne him' t ht) hcii
  have hQz : Q / ‖lam.1‖ ≤ Q := div_le_self hQ hz1
  have hDz : D / ‖lam.1‖ ^ 2 ≤ D := div_le_self hD (one_le_pow₀ hz1)
  have hmono : Real.exp (2 * τ) * (Real.exp τ * (Q / ‖lam.1‖) * ∫ t in (0 : ℝ)..1, ‖coverRep38
        (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t‖) ≤
      Real.exp (2 * τ) * (Real.exp τ * Q * ∫ t in (0 : ℝ)..1, ‖coverRep38
        (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t‖) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_right _ hCc
    exact mul_le_mul_of_nonneg_left hQz (Real.exp_pos _).le
  try beta_reduce at hP
  linarith

theorem off_bounded {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ M L : ℝ, 0 ≤ M ∧ 1 ≤ L ∧ ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ τ →
      ‖sourceRemainderVector φ b lam 1 (if b then 0 else 1)‖ ≤ M := by
  obtain ⟨O, L, hO, hL, hoff⟩ := NlsGge.ThirdConsultation.KSPS017W.off_approx hN φ b τ hτ
  have hcii : IntervalIntegrable (fun t => ‖coverRep38
      (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t‖) volume 0 1 :=
    (intervalIntegrable_of_memLp (NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc
      (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)))).norm
  have hCc : 0 ≤ ∫ t in (0 : ℝ)..1, ‖coverRep38
      (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t‖ :=
    intervalIntegral.integral_nonneg zero_le_one (fun t _ => norm_nonneg _)
  refine ⟨O + Real.exp τ * ∫ t in (0 : ℝ)..1, ‖coverRep38
      (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t‖, L,
    add_nonneg hO (mul_nonneg (Real.exp_pos _).le hCc), hL, fun lam hlam him => ?_⟩
  have hz1 : 1 ≤ ‖lam.1‖ := hL.trans hlam
  have h1 := hoff lam hlam him
  have htri := (norm_sub_norm_le _ _).trans h1
  have hκ : ‖(if b then -Complex.I else Complex.I)‖ = 1 := by cases b <;> simp
  have hμ : |((if b then (-1 : ℂ) else 1) * lam.1).im| ≤ τ := by
    cases b <;> simpa using him
  have hosc := norm_endpointOsc_mul_le hμ (q := fun _ => (1 : ℂ)) (Q := 1)
    (H := coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)))
    (fun t _ => by simp) hcii
  simp only [one_mul, mul_one] at hosc
  have hP : ‖(if b then -Complex.I else Complex.I) *
      endpointOsc ((if b then (-1 : ℂ) else 1) * lam.1)
        (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)))‖ ≤
      Real.exp τ * ∫ t in (0 : ℝ)..1, ‖coverRep38
        (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t‖ := by
    rw [norm_mul, hκ, one_mul]
    exact hosc
  have hOz : O / ‖lam.1‖ ≤ O := div_le_self hO hz1
  linarith

/-- Pro round 15 Q4 §1: the four endpoint remainder entries are bounded on a fixed strip. -/
theorem endpoint_remainders_bounded_on_strip
    (N : ℕ) (hN : 1 ≤ N) (φ : KSPS.SobolevC N)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ (M L : ℝ), 0 ≤ M ∧ 1 ≤ L ∧
      ∀ (z : ℂ) (hz : z ≠ 0), L ≤ ‖z‖ → |z.im| ≤ τ →
        ‖sourceRemainderVector φ false ⟨z, hz⟩ 1 0‖ ≤ M ∧
        ‖sourceRemainderVector φ true  ⟨z, hz⟩ 1 1‖ ≤ M ∧
        ‖sourceRemainderVector φ true  ⟨z, hz⟩ 1 0‖ ≤ M ∧
        ‖sourceRemainderVector φ false ⟨z, hz⟩ 1 1‖ ≤ M := by
  obtain ⟨M1, L1, hM1, hL1, h1⟩ := diag_false_bounded hN φ τ hτ
  obtain ⟨M2, L2, hM2, hL2, h2⟩ := diag_true_bounded hN φ τ hτ
  obtain ⟨M3, L3, hM3, hL3, h3⟩ := off_bounded hN φ true τ hτ
  obtain ⟨M4, L4, hM4, hL4, h4⟩ := off_bounded hN φ false τ hτ
  refine ⟨max (max M1 M2) (max M3 M4), max (max L1 L2) (max L3 L4),
    le_max_of_le_left (le_max_of_le_left hM1), le_max_of_le_left (le_max_of_le_left hL1),
    fun z hz hzL him => ?_⟩
  have hz1 : L1 ≤ ‖z‖ := (le_max_left _ _).trans ((le_max_left _ _).trans hzL)
  have hz2 : L2 ≤ ‖z‖ := (le_max_right _ _).trans ((le_max_left _ _).trans hzL)
  have hz3 : L3 ≤ ‖z‖ := (le_max_left _ _).trans ((le_max_right _ _).trans hzL)
  have hz4 : L4 ≤ ‖z‖ := (le_max_right _ _).trans ((le_max_right _ _).trans hzL)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (h1 ⟨z, hz⟩ hz1 him).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (h2 ⟨z, hz⟩ hz2 him).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (h3 ⟨z, hz⟩ hz3 him).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h4 ⟨z, hz⟩ hz4 him).trans ((le_max_right _ _).trans (le_max_right _ _))

end
end NlsGge.ThirdConsultation.KSPSWKB

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

/-- Pro round 15 Q4 §2: fixed-potential strip estimate for the discriminant against 2 cos(wkbPhase). -/
theorem discriminant_wkb_strip_bound
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ (C L : ℝ), 0 ≤ C ∧ 1 ≤ L ∧
      ∀ z : ℂ, L ≤ ‖z‖ → |z.im| ≤ τ →
        ‖discriminant φ z - 2 * Complex.cos (wkbPhase φ z)‖ ≤
          C / ‖z‖ ^ N := by
  obtain ⟨M, L0, hM, hL0, hrem⟩ := KSPSWKB.endpoint_remainders_bounded_on_strip N hN φ τ hτ
  set B : ℝ := sobolevNorm N φ with hBdef
  set S : ℝ := ∑ k ∈ Finset.Icc 1 N,
    NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B k with hSdef
  have hS0 : 0 ≤ S :=
    Finset.sum_nonneg (fun k hk => KSPSWKB.endpointCoefficientBound_nonneg N B k hk)
  refine ⟨6 * M, max L0 (NlsGge.ThirdConsultation.KSPSVolterra.threshold N B), by linarith,
    le_max_of_le_left hL0, fun z hzL him => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := hL0.trans ((le_max_left _ _).trans hzL)
  have hzT : NlsGge.ThirdConsultation.KSPSVolterra.threshold N B ≤ ‖z‖ :=
    (le_max_right _ _).trans hzL
  have hzS : 1 + S ≤ ‖z‖ := hzT
  have hzL0 : L0 ≤ ‖z‖ := (le_max_left _ _).trans hzL
  have hz : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz1
    norm_num at hz1
  have hX0 : 0 < ‖z‖ := by linarith
  have hthr : WKBThreshold N B z := ⟨hX0, hzT⟩
  have hdet := KSPSWKB.initialColumns_det_bound N B φ z le_rfl hthr
  have hdetv : Matrix.det (KSPSWKB.initialColumns φ z) =
      1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0 := by
    simp [KSPSWKB.initialColumns, Matrix.det_fin_two]
  rw [hdetv] at hdet
  have hD : 1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    norm_num at hdet
  have hid := NlsGge.ThirdConsultation.KSPS015W.disc_identity φ ⟨z, hz⟩
    (fun k hk => integrated_riccati_vanishing N k φ hk)
    (WKB_monodromy_entries N B φ ⟨z, hz⟩ le_rfl hthr).2 hD
  dsimp only at hid
  have hDinv : ‖(1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hpos : 0 < ‖1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0‖ := by linarith
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  have hε : ‖((2 * Complex.I * z) ^ N)⁻¹‖ = ((2 * ‖z‖) ^ N)⁻¹ := by
    rw [norm_inv, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  have hhalf : S / (2 * ‖z‖) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hα : ‖KSPSWKB.alpha φ z 0‖ ≤ 1 / 2 :=
    (KSPSWKB.endpointSum_norm_le B φ le_rfl false z hz1).trans hhalf
  have hβ : ‖KSPSWKB.beta φ z 0‖ ≤ 1 / 2 :=
    (KSPSWKB.endpointSum_norm_le B φ le_rfl true z hz1).trans hhalf
  obtain ⟨hr0, hr1, hs0, hs1⟩ := hrem z hz hzL0 him
  have hE : discriminant φ z - 2 * Complex.cos (wkbPhase φ z) =
      (1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0)⁻¹ * ((2 * Complex.I * z) ^ N)⁻¹ *
        (NlsGge.ThirdConsultation.KSPS015W.rf φ ⟨z, hz⟩ 0 + NlsGge.ThirdConsultation.KSPS015W.rt φ ⟨z, hz⟩ 1 -
          KSPSWKB.alpha φ z 0 * NlsGge.ThirdConsultation.KSPS015W.rt φ ⟨z, hz⟩ 0 -
          KSPSWKB.beta φ z 0 * NlsGge.ThirdConsultation.KSPS015W.rf φ ⟨z, hz⟩ 1) := by
    rw [hid]
    ring
  rw [hE]
  exact NlsGge.ThirdConsultation.KSPS031Analytic.discriminant_error_bound N ‖z‖ M _ _ _ _ _ _ _ _
    hz1 hM hDinv hε hr0 hr1 hs0 hs1 hα hβ

end
end NlsGge.ThirdConsultation.KSPS
