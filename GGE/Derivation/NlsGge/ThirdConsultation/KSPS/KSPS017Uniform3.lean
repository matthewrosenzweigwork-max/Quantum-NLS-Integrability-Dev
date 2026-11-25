import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS017Support9
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU4

/- KSPS017U3 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS017Uniform3.lean. Pro round-15 SUPPORT (never a packet), input h17U.
   Ball-uniform companion of KSPS017Support9.off_approx: ONE (C, L) for all φ with ‖φ.1‖+‖φ.2‖ ≤ KB and all φ' with
   sobolevNorm 1 φ' ≤ B, toPair φ' = toPotPair φ. Body = landed off_approx, re-quantified:
   the per-φ inputs are replaced by the exact conclusion bodies of the landed K-uniform producers, taken as
   hypotheses with their constants (C8, L8) = NlsGge.ThirdConsultation.KSPSWKB.sourceRemainder_endpoint_expansion_U, K = KSPSQ2.forcing_osc_U
   (Λ = L8), M1 = KSPSQ2.a1_osc_U (the glue discharges them; split only for the worker-lane memory cap);
   the φ-dependent continuity bound Q of q(t) = ∫₀ᵗ φ₁φ₂ is the explicit Q = KB² (as in KSPS011Quant4), and
   Cc = ∫‖c‖ ≤ (D² + 1)/2 with D = KSPSSupport.h161_coef_top. No hypothesis added. -/
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators Topology Interval

namespace NlsGge.ThirdConsultation.KSPS017U3
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS017W

theorem off_approx_U_of {N : ℕ} (hN : 1 ≤ N) (KB B : ℝ) (hKB : 0 ≤ KB) (hB : 0 ≤ B)
    (b : Bool) (a : ℝ) (ha : 0 ≤ a)
    (C8 L8 : ℝ) (hC8 : 0 ≤ C8) (hL8 : 0 < L8)
    (h8 : ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : NlsGge.ThirdConsultation.KSPS.SobolevC 1, NlsGge.ThirdConsultation.KSPS.sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = NlsGge.ThirdConsultation.KSPS.toPotPair φ →
      ∀ (b : Bool) (lam : {z : ℂ // z ≠ 0}), L8 ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ∀ f : PotPair,
        (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
          ![potRepFst38 f t, potRepSnd38 f t] = NlsGge.ThirdConsultation.KSPSWKB.sourceForcingVector φ b lam t) →
        ‖NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ b lam 1 -
            NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 -
            NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1‖ ≤
          C8 / ‖lam.1‖ ^ 2)
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB → ∀ (lam : ℂ), L8 ≤ ‖lam‖ →
      ∀ (μ : ℂ), |μ.im| ≤ a →
      ∀ (q : ℝ → ℂ) (Q : ℝ), ContinuousOn q (Icc (0 : ℝ) 1) → (∀ t ∈ Icc (0 : ℝ) 1, ‖q t‖ ≤ Q) →
      ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam t) -
        NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => q t * coverRep38
          (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t) -
        (2 * Complex.I * lam)⁻¹ * NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => q t *
          NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t)‖ ≤ Real.exp a * Q * K / ‖lam‖ ^ 2)
    (M1 : ℝ) (hM1 : 0 ≤ M1)
    (hM1b : ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB → ∀ (μ : ℂ), |μ.im| ≤ a →
      ∀ (q : ℝ → ℂ) (Q : ℝ), (∀ t ∈ Icc (0 : ℝ) 1, ‖q t‖ ≤ Q) →
      ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t)‖ ≤
        Real.exp a * Q * M1) :
    ∃ C L : ℝ, 0 ≤ C ∧ 1 ≤ L ∧ ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ‖NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ b lam 1 (if b then 0 else 1) -
        (if b then -Complex.I else Complex.I) *
          NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((if b then (-1 : ℂ) else 1) * lam.1)
            (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)))‖ ≤ C / ‖lam.1‖ := by
  obtain ⟨D, hD0, hTop⟩ := NlsGge.ThirdConsultation.KSPSSupport.h161_coef_top N hN KB hKB
  set Q : ℝ := KB ^ 2 with hQdef
  have hQ0 : 0 ≤ Q := sq_nonneg _
  set Cu : ℝ := (D ^ 2 + 1) / 2 with hCudef
  have hCu : 0 ≤ Cu := by positivity
  set ea : ℝ := Real.exp a with headef
  have hea : 0 < ea := Real.exp_pos a
  set D1 : ℝ := ea * (M1 / 2 + K) with hD1
  set BF : ℝ := ea * Cu + D1 with hBF
  set BqF : ℝ := ea * Q * Cu + Q * D1 with hBqF
  have hD10 : 0 ≤ D1 := by positivity
  refine ⟨C8 + D1 + (Q * BF + BqF) / 2, max L8 1, by positivity, le_max_right _ _,
    fun φ hS φ' hφB hφ' lam hL him => ?_⟩
  set c : PhysicalL2 := NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1) with hcdef
  set q : ℝ → ℂ := fun t => NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ' t 0 0 with hqdef
  have hqc : ContinuousOn q (Icc (0 : ℝ) 1) := by
    simp only [hqdef, NlsGge.ThirdConsultation.KSPSWKB.integratedQuadratic_apply00]
    exact NlsGge.ThirdConsultation.KSPSSupport.h150_prim_continuousOn
      (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').1 (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').2
  have hQ : ∀ t ∈ Icc (0 : ℝ) 1, ‖q t‖ ≤ Q := by
    intro t ht
    simp only [hqdef, NlsGge.ThirdConsultation.KSPSWKB.integratedQuadratic_apply00]
    have h := NlsGge.ThirdConsultation.KSPSSupport.h161_prefix_le
      (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').1 (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').2 ht
    have e1 : ‖(NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').1‖ ≤ KB := by
      rw [hφ']
      exact (NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le N φ.1).trans
        (by linarith [norm_nonneg φ.2])
    have e2 : ‖(NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').2‖ ≤ KB := by
      rw [hφ']
      exact (NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le N φ.2).trans
        (by linarith [norm_nonneg φ.1])
    have e1s := pow_le_pow_left₀ (norm_nonneg _) e1 2
    have e2s := pow_le_pow_left₀ (norm_nonneg _) e2 2
    unfold potRepFst38 potRepSnd38
    rw [hQdef]
    linarith
  have hcmem : MemLp (coverRep38 c) 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc c
  have hcii : IntervalIntegrable (fun t => ‖coverRep38 c t‖) volume 0 1 :=
    (NlsGge.ThirdConsultation.KSPSWKB.intervalIntegrable_of_memLp hcmem).norm
  set Cc : ℝ := ∫ t in (0 : ℝ)..1, ‖coverRep38 c t‖ with hCcdef
  have hCc : 0 ≤ Cc := intervalIntegral.integral_nonneg zero_le_one (fun t _ => norm_nonneg _)
  have hcD : ‖c‖ ≤ D := by
    have h := hTop φ hS b
    rw [Nat.sub_self, Nat.cast_zero, NlsGge.ThirdConsultation.KSPSSupport.h161_norm_eq_psn0] at h
    exact h
  have hCcu : Cc ≤ Cu := by
    refine (NlsGge.ThirdConsultation.KSPSU4.integral_norm_coverRep_le c).trans ?_
    have : ‖c‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcD 2
    rw [hCudef]; linarith
  have hL8' : L8 ≤ ‖lam.1‖ := (le_max_left _ _).trans hL
  have hl1 : 1 ≤ ‖lam.1‖ := (le_max_right _ _).trans hL
  have hl0 : 0 < ‖lam.1‖ := by linarith
  set σc : ℂ := if b then (-1 : ℂ) else 1 with hσc
  set κ : ℂ := if b then -Complex.I else Complex.I with hκdef
  have hκ : ‖κ‖ = 1 := by cases b <;> simp [hκdef]
  set μ : ℂ := σc * lam.1 with hμdef
  have hμ : |μ.im| ≤ a := by cases b <;> simpa [hμdef, hσc] using him
  set F : ℝ → ℂ := NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam.1 with hFdef
  obtain ⟨f, hf⟩ := NlsGge.ThirdConsultation.KSPSWKB.exists_forcing_potPair φ b lam
  -- the forced expansion, component idx_b
  have hv := h8 φ hS φ' hφB hφ' b lam hL8' him f hf
  have hU : ‖NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ b lam 1 (if b then 0 else 1) -
      (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) (if b then 0 else 1)‖ ≤
      C8 / ‖lam.1‖ ^ 2 := by
    refine le_trans ?_ hv
    have e : (NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ b lam 1 -
        NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 -
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) (if b then 0 else 1) =
        NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ b lam 1 (if b then 0 else 1) -
        (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
          NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) (if b then 0 else 1) := by
      simp only [Pi.sub_apply, Pi.add_apply, sub_sub]
    rw [← e]
    exact norm_le_pi_norm _ _
  have hcomp := NlsGge.ThirdConsultation.KSPSWKB.comp_formula φ φ' b lam f hf
  -- oscillatory bounds
  have hone : ∀ t ∈ Icc (0 : ℝ) 1, ‖(fun _ : ℝ => (1 : ℂ)) t‖ ≤ 1 := fun t _ => by simp
  have hF1 := hK φ hS lam.1 hL8' μ hμ (fun _ => (1 : ℂ)) 1 continuousOn_const hone
  have hA1 := hM1b φ hS μ hμ (fun _ => (1 : ℂ)) 1 hone
  have hcb0 : ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => (fun _ : ℝ => (1 : ℂ)) t * coverRep38 c t)‖ ≤ ea * 1 * Cc :=
    NlsGge.ThirdConsultation.KSPSWKB.norm_endpointOsc_mul_le hμ hone hcii
  have hcb : ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => (fun _ : ℝ => (1 : ℂ)) t * coverRep38 c t)‖ ≤ ea * 1 * Cu :=
    hcb0.trans (mul_le_mul_of_nonneg_left hCcu (by positivity))
  have hFq := hK φ hS lam.1 hL8' μ hμ q Q hqc hQ
  have hAq := hM1b φ hS μ hμ q Q hQ
  have hcq0 : ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => q t * coverRep38 c t)‖ ≤ ea * Q * Cc :=
    NlsGge.ThirdConsultation.KSPSWKB.norm_endpointOsc_mul_le hμ hQ hcii
  have hcq : ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => q t * coverRep38 c t)‖ ≤ ea * Q * Cu :=
    hcq0.trans (mul_le_mul_of_nonneg_left hCcu (by positivity))
  simp only [one_mul] at hF1 hA1 hcb
  have hFF := osc_diff_pure lam.1 (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ F) (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (coverRep38 c))
    (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b)) ea 1 K M1 D1 hl1 hea.le zero_le_one hK0
    hD1 hF1 hA1
  have hqFF := osc_diff_pure lam.1 (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => q t * F t))
    (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => q t * coverRep38 c t))
    (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t)) ea Q K M1 D1 hl1 hea.le
    hQ0 hK0 hD1 hFq hAq
  have hk1 : 1 * D1 / ‖lam.1‖ ≤ D1 := by rw [one_mul]; exact div_le_self hD10 hl1
  have hkQ : Q * D1 / ‖lam.1‖ ≤ Q * D1 := div_le_self (by positivity) hl1
  have hBFb : ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ F‖ ≤ BF := by
    have h1 := norm_sub_norm_le (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ F) (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (coverRep38 c))
    have h2 : ea * 1 * Cu = ea * Cu := by ring
    rw [hBF]
    linarith only [h1, h2, hk1, hFF, hcb]
  have hBqFb : ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => q t * F t)‖ ≤ BqF := by
    have h1 := norm_sub_norm_le (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => q t * F t))
      (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => q t * coverRep38 c t))
    rw [hBqF]
    linarith only [h1, hkQ, hqFF, hcq]
  have hOF : ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ F - NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (coverRep38 c)‖ ≤ D1 / ‖lam.1‖ := by
    rw [← one_mul D1]; exact hFF
  have hq1 : ‖NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ' 1 0 0‖ ≤ Q :=
    hQ 1 ⟨zero_le_one, le_rfl⟩
  exact off_pure lam.1 _ _ (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ F) (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (coverRep38 c))
    (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc μ (fun t => q t * F t)) _ κ C8 D1 BF BqF Q hl1 hC8 hQ0 (by positivity) (by positivity)
    hU hcomp hκ hOF hBFb hBqFb hq1

end
end NlsGge.ThirdConsultation.KSPS017U3
