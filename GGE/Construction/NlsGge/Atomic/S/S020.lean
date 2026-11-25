import Mathlib
import NlsGge.Schur.ActualSchurCenterHolomorphic38V1
import NlsGge.Schur.ActualSchurCenterAnalytic38V1
import NlsGge.Schur.ActualSchurRealTypeCenter38V1
import NlsGge.ThirdConsultation.S.SShared06

                                                                                                                                                                                            
                                                                                                                                                                                                 
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem schurCenter_spec :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (n : ℤ),
      K * R ^ 3 ≤ |(n : ℝ)| → ∀ (p : SchurPair), ‖p‖ ≤ R →
      centerAt (2 * R) n p ∈ Metric.closedBall (spectralCenter n) (1 / 2) ∧
      centerAt (2 * R) n p = centerMapAt n p (centerAt (2 * R) n p) ∧
      (∀ t ∈ Metric.closedBall (spectralCenter n) (1 / 2),
        t = centerMapAt n p t → t = centerAt (2 * R) n p) ∧
      AnalyticAt ℂ (centerAt (2 * R) n) p ∧
      (∀ w : SchurH1, p = schurRealPair w → (centerAt (2 * R) n p).im = 0) := by
  refine ⟨8 * max actualSchurCenterThresholdConstant38 1,
    mul_pos (by norm_num) (lt_of_lt_of_le one_pos (le_max_right _ _)), ?_⟩
  intro R hR n hK p hp
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have h2R : (1 : ℝ) ≤ 2 * R := by linarith
  have hthr : actualSchurCenterThresholdConstant38 * (2 * R) ^ 3 ≤ |(n : ℝ)| := by
    have hc : actualSchurCenterThresholdConstant38 ≤ max actualSchurCenterThresholdConstant38 1 :=
      le_max_left _ _
    have hpos : (0 : ℝ) ≤ 8 * R ^ 3 := by positivity
    calc actualSchurCenterThresholdConstant38 * (2 * R) ^ 3
        = actualSchurCenterThresholdConstant38 * (8 * R ^ 3) := by ring
      _ ≤ max actualSchurCenterThresholdConstant38 1 * (8 * R ^ 3) :=
          mul_le_mul_of_nonneg_right hc hpos
      _ = 8 * max actualSchurCenterThresholdConstant38 1 * R ^ 3 := by ring
      _ ≤ |(n : ℝ)| := hK
  have hfst : ‖p.1‖ ≤ R := le_trans (norm_fst_le p) hp
  have hsnd : ‖p.2‖ ≤ R := le_trans (norm_snd_le p) hp
  have hp₁ : ‖p.1‖ ≤ 2 * R := by linarith
  have hp₂ : ‖p.2‖ ≤ 2 * R := by linarith
  obtain ⟨hball, hfix⟩ := actualSchurCenter38_spec (2 * R) h2R n hthr p hp₁ hp₂
  refine ⟨hball, hfix, ?_, ?_, ?_⟩
  · intro t ht htfix
    exact (actualSchurCenter38_eq_of_fixed (2 * R) h2R n hthr p hp₁ hp₂ t ht htfix).symm
  · exact actualSchurCenter38_analyticAt (2 * R) h2R n hthr p (by linarith) (by linarith)
  · intro w hwp
    subst hwp
    have hw : ‖w‖ ≤ 2 * R := by
      have h1 : ‖w‖ ≤ ‖schurRealPair w‖ := norm_fst_le (schurRealPair w)
      linarith
    exact actualSchurCenter38_real_realType (2 * R) h2R n hthr w hw

end NlsGge.ThirdConsultation.S
