import Mathlib
import NlsGge.Schur.ActualSchurOwnModeAssembly38V1
import NlsGge.Schur.ActualSchurCenterHolomorphic38V1
import NlsGge.Schur.ActualSchurCenterContraction38V1
import NlsGge.ThirdConsultation.S.SShared06

                                                                                                                                                                                        
                                                                                                                                                                                                 
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
open NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations
namespace NlsGge.ThirdConsultation.S

theorem center_ownMode_derivative :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (n : ℤ),
      K * R ^ 3 ≤ |(n : ℝ)| → ∀ (p : SchurPair), ‖p‖ ≤ R →
      let σ := centerAt (2 * R) n p
      let a := deriv (fun z : ℂ => alphaAt n z p) σ
      (3 / 4 : ℝ) ≤ ‖1 - a‖ ∧
      ownDerivative (centerAt (2 * R) n) n p =
        ownDerivative (fun q : SchurPair => alphaAt n σ q) n p / (1 - a) := by
  refine ⟨8 * max actualSchurCenterThresholdConstant38 1,
    mul_pos (by norm_num) (lt_of_lt_of_le one_pos (le_max_right _ _)), ?_⟩
  intro R hR n hKn p hpR
  have hR2 : (1 : ℝ) ≤ 2 * R := by linarith
  have hc : actualSchurCenterThresholdConstant38 * (2 * R) ^ 3 ≤ |(n : ℝ)| := by
    have h1 : actualSchurCenterThresholdConstant38 ≤ max actualSchurCenterThresholdConstant38 1 :=
      le_max_left _ _
    have h3 : 0 ≤ R ^ 3 := by positivity
    have h4 := mul_le_mul_of_nonneg_right h1 h3
    have h5 : actualSchurCenterThresholdConstant38 * (2 * R) ^ 3 =
        8 * (actualSchurCenterThresholdConstant38 * R ^ 3) := by ring
    linarith
  obtain ⟨hn, hlarge, -, h14⟩ :=
    actualSchurCenterThresholdConstant38_consequences (2 * R) hR2 n hc
  have hp₁ : ‖p.1‖ < 2 * R := lt_of_le_of_lt (le_trans (norm_fst_le p) hpR) (by linarith)
  have hp₂ : ‖p.2‖ < 2 * R := lt_of_le_of_lt (le_trans (norm_snd_le p) hpR) (by linarith)
  obtain ⟨hσD, -⟩ := actualSchurCenter38_spec (2 * R) hR2 n hc p hp₁.le hp₂.le
  have hσS : actualSchurCenter38 (2 * R) n p ∈ spectralDisk n :=
    closedBall_half_subset_spectralDisk38 n hσD
  have hJ := actualSchurCoefficient_hasFDerivAt_center38 (2 * R) hR2 n hc
    (true, resonantIndex n) (true, resonantIndex n) p hp₁ hp₂
  have hz : HasFDerivAt (fun z : ℂ => (z, p))
      (ContinuousLinearMap.inl ℂ ℂ SchurPair) (centerAt (2 * R) n p) :=
    (hasFDerivAt_id _).prodMk (hasFDerivAt_const p _)
  have hA1 : HasDerivAt (fun z : ℂ => alphaAt n z p)
      (actualSchurCoefficientJointDeriv38 (2 * R) n (true, resonantIndex n)
        (true, resonantIndex n) p (1, 0)) (centerAt (2 * R) n p) :=
    (hJ.comp (centerAt (2 * R) n p) hz).hasDerivAt
  have ha_eq : deriv (fun z : ℂ => alphaAt n z p) (centerAt (2 * R) n p) =
      actualSchurCoefficientJointDeriv38 (2 * R) n (true, resonantIndex n)
        (true, resonantIndex n) p (1, 0) :=
    hA1.deriv
  have hdA := actualSchurAlpha38_hasDerivAt (2 * R) hR2 n hn hlarge p
    (actualSchurCenter38 (2 * R) n p) hσS hp₁.le hp₂.le
  have hA1' : HasDerivAt (actualSchurAlpha38 n p)
      (actualSchurCoefficientJointDeriv38 (2 * R) n (true, resonantIndex n)
        (true, resonantIndex n) p (1, 0)) (actualSchurCenter38 (2 * R) n p) := hA1
  have hu := hA1'.unique hdA
  have hbd := actualSchurAlpha38_deriv_bound (2 * R) hR2 n hn hlarge p
    (actualSchurCenter38 (2 * R) n p) hσS hp₁.le hp₂.le
  have ha_le : ‖actualSchurCoefficientJointDeriv38 (2 * R) n (true, resonantIndex n)
      (true, resonantIndex n) p (1, 0)‖ ≤ 1 / 4 := by
    rw [hu]
    exact le_trans hbd h14
  have h34 : (3 / 4 : ℝ) ≤ ‖1 - actualSchurCoefficientJointDeriv38 (2 * R) n
      (true, resonantIndex n) (true, resonantIndex n) p (1, 0)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (actualSchurCoefficientJointDeriv38 (2 * R) n
      (true, resonantIndex n) (true, resonantIndex n) p (1, 0))
    rw [norm_one] at h
    linarith
  have hne : (1 - actualSchurCoefficientJointDeriv38 (2 * R) n (true, resonantIndex n)
      (true, resonantIndex n) p (1, 0)) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h34
    linarith
  have hN : HasFDerivAt (fun q : SchurPair => alphaAt n (centerAt (2 * R) n p) q)
      ((actualSchurCoefficientJointDeriv38 (2 * R) n (true, resonantIndex n)
        (true, resonantIndex n) p).comp (ContinuousLinearMap.inr ℂ ℂ SchurPair)) p :=
    hJ.comp p ((hasFDerivAt_const (centerAt (2 * R) n p) p).prodMk (hasFDerivAt_id p))
  have hNum : ownDerivative (fun q : SchurPair => alphaAt n (centerAt (2 * R) n p) q) n p =
      actualSchurCoefficientJointDeriv38 (2 * R) n (true, resonantIndex n)
        (true, resonantIndex n) p (0, ownDirection n) := by
    unfold ownDerivative
    rw [hN.fderiv]
    rfl
  have hEq : (1 - actualSchurCoefficientJointDeriv38 (2 * R) n (true, resonantIndex n)
      (true, resonantIndex n) p (1, 0)) * fderiv ℂ (centerAt (2 * R) n) p (ownDirection n) =
      actualSchurCoefficientJointDeriv38 (2 * R) n (true, resonantIndex n)
        (true, resonantIndex n) p (0, ownDirection n) :=
    actualSchurCenter38_fderiv_equation (2 * R) hR2 n hc p hp₁ hp₂ (ownDirection n)
  dsimp only
  rw [ha_eq, hNum]
  refine ⟨h34, ?_⟩
  unfold ownDerivative
  rw [eq_div_iff hne]
  linear_combination hEq

end NlsGge.ThirdConsultation.S
