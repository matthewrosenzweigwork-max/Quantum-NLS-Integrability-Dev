import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS017Support4
import NlsGge.ThirdConsultation.KSPS.KSPS011Support14

/- KSPS-017 SUPPORT9 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS017Support9.lean.
   (Split off from the first KSPS017Support4 draft, unchanged code.) UNIFORM strip approximation of the off-diagonal
   endpoint remainder, |R_b(lam,1)_{idx_b} - kappa_b endpointOsc(sigma_b lam, c_b)| <= C/|lam| for |lam| >= L,
   |Im lam| <= a, c_b = top Riccati coefficient (lam-independent), from the landed KSPS-011 chain:
   sourceRemainder_endpoint_expansion (KSPS-007 forced expansion), comp_formula, forcing_osc_expansion,
   a1_osc_bound; osc_diff_pure / off_pure are the pure inequalities. -/
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators Topology Interval

namespace NlsGge.ThirdConsultation.KSPS017W
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS

theorem osc_diff_pure (lam G Gc Ga : ℂ) (ea QQ K M1 D1 : ℝ) (hl1 : 1 ≤ ‖lam‖) (hea : 0 ≤ ea) (hQQ : 0 ≤ QQ)
    (hK : 0 ≤ K) (hD1 : D1 = ea * (M1 / 2 + K))
    (h1 : ‖G - Gc - (2 * Complex.I * lam)⁻¹ * Ga‖ ≤ ea * QQ * K / ‖lam‖ ^ 2)
    (h2 : ‖Ga‖ ≤ ea * QQ * M1) : ‖G - Gc‖ ≤ QQ * D1 / ‖lam‖ := by
  have hl0 : 0 < ‖lam‖ := by linarith
  have hinv : ‖(2 * Complex.I * lam)⁻¹‖ = 1 / (2 * ‖lam‖) := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one, one_div]
  have hsq : 1 / ‖lam‖ ^ 2 ≤ 1 / ‖lam‖ := one_div_le_one_div_of_le hl0 (le_self_pow₀ hl1 two_ne_zero)
  have e : G - Gc = (G - Gc - (2 * Complex.I * lam)⁻¹ * Ga) + (2 * Complex.I * lam)⁻¹ * Ga := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, hinv]
  have k1 : ea * QQ * K / ‖lam‖ ^ 2 ≤ ea * QQ * K / ‖lam‖ := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div (ea * QQ * K)]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have k2 : 1 / (2 * ‖lam‖) * ‖Ga‖ ≤ ea * QQ * M1 / 2 / ‖lam‖ := by
    calc 1 / (2 * ‖lam‖) * ‖Ga‖ ≤ 1 / (2 * ‖lam‖) * (ea * QQ * M1) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ea * QQ * M1 / 2 / ‖lam‖ := by field_simp
  have k3 : ea * QQ * K / ‖lam‖ + ea * QQ * M1 / 2 / ‖lam‖ = QQ * D1 / ‖lam‖ := by
    rw [hD1]; field_simp; ring
  linarith

theorem off_pure (lam R LF OF Oc OqF q1 κ : ℂ) (C8 D1 BF BqF Q : ℝ) (hl1 : 1 ≤ ‖lam‖)
    (hC8 : 0 ≤ C8) (hQ : 0 ≤ Q) (hBF : 0 ≤ BF) (hBqF : 0 ≤ BqF)
    (hR : ‖R - LF‖ ≤ C8 / ‖lam‖ ^ 2) (hLF : LF = κ * OF + (2 * lam)⁻¹ * (q1 * OF - OqF)) (hκ : ‖κ‖ = 1)
    (hOF : ‖OF - Oc‖ ≤ D1 / ‖lam‖) (hOFb : ‖OF‖ ≤ BF) (hOqF : ‖OqF‖ ≤ BqF) (hq1 : ‖q1‖ ≤ Q) :
    ‖R - κ * Oc‖ ≤ (C8 + D1 + (Q * BF + BqF) / 2) / ‖lam‖ := by
  have hl0 : 0 < ‖lam‖ := by linarith
  have hsq : 1 / ‖lam‖ ^ 2 ≤ 1 / ‖lam‖ := one_div_le_one_div_of_le hl0 (le_self_pow₀ hl1 two_ne_zero)
  have hsplit : R - κ * Oc = (R - LF) + κ * (OF - Oc) + (2 * lam)⁻¹ * (q1 * OF - OqF) := by rw [hLF]; ring
  have hinv2 : ‖(2 * lam)⁻¹‖ = 1 / (2 * ‖lam‖) := by
    rw [norm_inv, norm_mul, Complex.norm_ofNat, one_div]
  have t2 : ‖κ * (OF - Oc)‖ ≤ D1 / ‖lam‖ := by rw [norm_mul, hκ, one_mul]; exact hOF
  have hin : ‖q1 * OF - OqF‖ ≤ Q * BF + BqF := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul hq1 hOFb (norm_nonneg _) hQ
    linarith
  have t3 : ‖(2 * lam)⁻¹ * (q1 * OF - OqF)‖ ≤ (Q * BF + BqF) / 2 / ‖lam‖ := by
    rw [norm_mul, hinv2]
    calc 1 / (2 * ‖lam‖) * ‖q1 * OF - OqF‖ ≤ 1 / (2 * ‖lam‖) * (Q * BF + BqF) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = (Q * BF + BqF) / 2 / ‖lam‖ := by field_simp
  have t1 : C8 / ‖lam‖ ^ 2 ≤ C8 / ‖lam‖ := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div C8]; exact mul_le_mul_of_nonneg_left hsq hC8
  rw [hsplit]
  have a1 := norm_add_le ((R - LF) + κ * (OF - Oc)) ((2 * lam)⁻¹ * (q1 * OF - OqF))
  have a2 := norm_add_le (R - LF) (κ * (OF - Oc))
  have e : (C8 + D1 + (Q * BF + BqF) / 2) / ‖lam‖ = C8 / ‖lam‖ + D1 / ‖lam‖ + (Q * BF + BqF) / 2 / ‖lam‖ := by
    ring
  rw [e]
  linarith

/-- Uniform strip approximation of the off-diagonal endpoint remainder (order 1/|lam|). -/
theorem off_approx {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) (a : ℝ) (ha : 0 ≤ a) :
    ∃ C L : ℝ, 0 ≤ C ∧ 1 ≤ L ∧ ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ‖KSPSWKB.sourceRemainderVector φ b lam 1 (if b then 0 else 1) -
        (if b then -Complex.I else Complex.I) *
          KSPSWKB.endpointOsc ((if b then (-1 : ℂ) else 1) * lam.1)
            (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)))‖ ≤ C / ‖lam.1‖ := by
  obtain ⟨φ', hφ'⟩ := NlsGge.ThirdConsultation.KSPS011Support4.exists_toPair_eq hN φ
  set c : PhysicalL2 := NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1) with hcdef
  set q : ℝ → ℂ := fun t => NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ' t 0 0 with hqdef
  have hqc : ContinuousOn q (Icc (0 : ℝ) 1) := by
    simp only [hqdef, KSPSWKB.integratedQuadratic_apply00]
    exact NlsGge.ThirdConsultation.KSPSSupport.h150_prim_continuousOn
      (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').1 (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').2
  obtain ⟨Q, hQ⟩ := isCompact_Icc.exists_bound_of_continuousOn hqc
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨C8, L8, hC8, hL8, h8⟩ := KSPSWKB.sourceRemainder_endpoint_expansion hN φ φ' hφ' a ha
  obtain ⟨K, hK0, hK⟩ := KSPSWKB.forcing_osc_expansion hN φ b a L8 hL8
  obtain ⟨M1, hM1, hM1b⟩ := KSPSWKB.a1_osc_bound hN φ b a
  have hcmem : MemLp (coverRep38 c) 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc c
  have hcii : IntervalIntegrable (fun t => ‖coverRep38 c t‖) volume 0 1 :=
    (KSPSWKB.intervalIntegrable_of_memLp hcmem).norm
  set Cc : ℝ := ∫ t in (0 : ℝ)..1, ‖coverRep38 c t‖ with hCcdef
  have hCc : 0 ≤ Cc := intervalIntegral.integral_nonneg zero_le_one (fun t _ => norm_nonneg _)
  set ea : ℝ := Real.exp a with headef
  have hea : 0 < ea := Real.exp_pos a
  set D1 : ℝ := ea * (M1 / 2 + K) with hD1
  set BF : ℝ := ea * Cc + D1 with hBF
  set BqF : ℝ := ea * Q * Cc + Q * D1 with hBqF
  have hD10 : 0 ≤ D1 := by positivity
  refine ⟨C8 + D1 + (Q * BF + BqF) / 2, max L8 1, by positivity, le_max_right _ _, fun lam hL him => ?_⟩
  have hL8' : L8 ≤ ‖lam.1‖ := (le_max_left _ _).trans hL
  have hl1 : 1 ≤ ‖lam.1‖ := (le_max_right _ _).trans hL
  have hl0 : 0 < ‖lam.1‖ := by linarith
  set σc : ℂ := if b then (-1 : ℂ) else 1 with hσc
  set κ : ℂ := if b then -Complex.I else Complex.I with hκdef
  have hκ : ‖κ‖ = 1 := by cases b <;> simp [hκdef]
  set μ : ℂ := σc * lam.1 with hμdef
  have hμ : |μ.im| ≤ a := by cases b <;> simpa [hμdef, hσc] using him
  set F : ℝ → ℂ := NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam.1 with hFdef
  obtain ⟨f, hf⟩ := KSPSWKB.exists_forcing_potPair φ b lam
  -- the forced expansion, component idx_b
  have hv := h8 b lam hL8' him f hf
  have hU : ‖KSPSWKB.sourceRemainderVector φ b lam 1 (if b then 0 else 1) -
      (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) (if b then 0 else 1)‖ ≤
      C8 / ‖lam.1‖ ^ 2 := by
    refine le_trans ?_ hv
    have e : (KSPSWKB.sourceRemainderVector φ b lam 1 -
        NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 -
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) (if b then 0 else 1) =
        KSPSWKB.sourceRemainderVector φ b lam 1 (if b then 0 else 1) -
        (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
          NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) (if b then 0 else 1) := by
      simp only [Pi.sub_apply, Pi.add_apply, sub_sub]
    rw [← e]
    exact norm_le_pi_norm _ _
  have hcomp := KSPSWKB.comp_formula φ φ' b lam f hf
  -- oscillatory bounds
  have hone : ∀ t ∈ Icc (0 : ℝ) 1, ‖(fun _ : ℝ => (1 : ℂ)) t‖ ≤ 1 := fun t _ => by simp
  have hF1 := hK lam.1 hL8' μ hμ (fun _ => (1 : ℂ)) 1 continuousOn_const hone
  have hA1 := hM1b μ hμ (fun _ => (1 : ℂ)) 1 hone
  have hcb : ‖KSPSWKB.endpointOsc μ (fun t => (fun _ : ℝ => (1 : ℂ)) t * coverRep38 c t)‖ ≤ ea * 1 * Cc :=
    KSPSWKB.norm_endpointOsc_mul_le hμ hone hcii
  have hFq := hK lam.1 hL8' μ hμ q Q hqc hQ
  have hAq := hM1b μ hμ q Q hQ
  have hcq : ‖KSPSWKB.endpointOsc μ (fun t => q t * coverRep38 c t)‖ ≤ ea * Q * Cc :=
    KSPSWKB.norm_endpointOsc_mul_le hμ hQ hcii
  simp only [one_mul] at hF1 hA1 hcb
  have hFF := osc_diff_pure lam.1 (KSPSWKB.endpointOsc μ F) (KSPSWKB.endpointOsc μ (coverRep38 c))
    (KSPSWKB.endpointOsc μ (NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b)) ea 1 K M1 D1 hl1 hea.le zero_le_one hK0
    hD1 hF1 hA1
  have hqFF := osc_diff_pure lam.1 (KSPSWKB.endpointOsc μ (fun t => q t * F t))
    (KSPSWKB.endpointOsc μ (fun t => q t * coverRep38 c t))
    (KSPSWKB.endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t)) ea Q K M1 D1 hl1 hea.le
    hQ0 hK0 hD1 hFq hAq
  have hk1 : 1 * D1 / ‖lam.1‖ ≤ D1 := by rw [one_mul]; exact div_le_self hD10 hl1
  have hkQ : Q * D1 / ‖lam.1‖ ≤ Q * D1 := div_le_self (by positivity) hl1
  have hBFb : ‖KSPSWKB.endpointOsc μ F‖ ≤ BF := by
    have h1 := norm_sub_norm_le (KSPSWKB.endpointOsc μ F) (KSPSWKB.endpointOsc μ (coverRep38 c))
    have h2 : ea * 1 * Cc = ea * Cc := by ring
    rw [hBF]
    linarith only [h1, h2, hk1, hFF, hcb]
  have hBqFb : ‖KSPSWKB.endpointOsc μ (fun t => q t * F t)‖ ≤ BqF := by
    have h1 := norm_sub_norm_le (KSPSWKB.endpointOsc μ (fun t => q t * F t))
      (KSPSWKB.endpointOsc μ (fun t => q t * coverRep38 c t))
    rw [hBqF]
    linarith only [h1, hkQ, hqFF, hcq]
  have hOF : ‖KSPSWKB.endpointOsc μ F - KSPSWKB.endpointOsc μ (coverRep38 c)‖ ≤ D1 / ‖lam.1‖ := by
    rw [← one_mul D1]; exact hFF
  have hq1 : ‖NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ' 1 0 0‖ ≤ Q :=
    hQ 1 ⟨zero_le_one, le_rfl⟩
  exact off_pure lam.1 _ _ (KSPSWKB.endpointOsc μ F) (KSPSWKB.endpointOsc μ (coverRep38 c))
    (KSPSWKB.endpointOsc μ (fun t => q t * F t)) _ κ C8 D1 BF BqF Q hl1 hC8 hQ0 (by positivity) (by positivity)
    hU hcomp hκ hOF hBFb hBqFb hq1

end
end NlsGge.ThirdConsultation.KSPS017W
