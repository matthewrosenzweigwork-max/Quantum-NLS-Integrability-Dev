import NlsGge.GK38.GradTauGammaMomentIBP
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual parameter differentiation of periodic moments, followed by their
independent discriminant quotient contour representation. -/
set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

def k4aMomentPartial38 (φ : PotPair) (k : ℕ) (z : ℂ) : PotPair →L[ℂ] ℂ :=
  Lib.paramCircleDerivative38 (fun ψ => momentIntegrand38 ψ k) φ z

def k4aQuotientCLM38 (φ : PotPair) (z : ℂ) : PotPair →L[ℂ] ℂ :=
  (discrim φ z / perChar φ z) • gradDiscrimCLM φ z

theorem k4aMomentPartial_joint_analytic38 (k : ℕ) :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => k4aMomentPartial38 p.1 k p.2)
      {p : PotPair × ℂ | perChar p.1 p.2 ≠ 0} := by
  let F : PotPair × ℂ → ℂ := Function.uncurry (fun ψ => momentIntegrand38 ψ k)
  let T : ((PotPair × ℂ) →L[ℂ] ℂ) →L[ℂ] (PotPair →L[ℂ] ℂ) :=
    (ContinuousLinearMap.compL ℂ PotPair (PotPair × ℂ) ℂ).flip
      (ContinuousLinearMap.inl ℂ PotPair ℂ)
  intro p hp
  have hA : AnalyticAt ℂ F p :=
    ((analyticAt_snd.pow k).mul (analyticOnNhd_perCharDeriv_joint38 p (mem_univ _))).div
      (analyticOnNhd_perChar_joint38 p (mem_univ _)) hp
  exact (T.analyticAt _).comp hA.fderiv

theorem k4aMomentPartial_circleIntegrable38 (φ : PotPair) (k : ℕ)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (k4aMomentPartial38 φ k) (C n) (R n) := by
  have hA : AnalyticOnNhd ℂ (k4aMomentPartial38 φ k) {z : ℂ | perChar φ z ≠ 0} := by
    intro z hz
    exact (k4aMomentPartial_joint_analytic38 k (φ, z) hz).comp
      ((analyticAt_const (v := φ)).prod analyticAt_id)
  exact (hA.continuousOn.mono (fun z hz => isolating_periodic_boundary38 hf n z hz)).circleIntegrable
    (isolating_radius_pos38 hf n).le

theorem k4aQuotientCLM_joint_analytic38 :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => k4aQuotientCLM38 p.1 p.2)
      {p : PotPair × ℂ | perChar p.1 p.2 ≠ 0} := by
  intro p hp
  exact ((analyticOnNhd_discrim p (mem_univ _)).div
    (analyticOnNhd_perChar_joint38 p (mem_univ _)) hp).smul
      (ActionGradient.gradDiscrim_joint_analytic p (mem_univ _))

theorem k4aQuotientCLM_circleIntegrable38 (φ : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (k4aQuotientCLM38 φ) (C n) (R n) := by
  have hA : AnalyticOnNhd ℂ (k4aQuotientCLM38 φ) {z : ℂ | perChar φ z ≠ 0} := by
    intro z hz
    exact (k4aQuotientCLM_joint_analytic38 (φ, z) hz).comp
      ((analyticAt_const (v := φ)).prod analyticAt_id)
  exact (hA.continuousOn.mono (fun z hz => isolating_periodic_boundary38 hf n z hz)).circleIntegrable
    (isolating_radius_pos38 hf n).le

theorem k4aFixedMoment_hasFDeriv38 (V : Set PotPair) (hVo : IsOpen V)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : ∀ ψ ∈ V, IsolatingFamily38 ψ C R)
    (φ : PotPair) (hφV : φ ∈ V) (n : ℤ) (k : ℕ) :
    HasFDerivAt (fun ψ => fixedMoment38 ψ C R n k)
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        circleIntegral (k4aMomentPartial38 φ k) (C n) (R n)) φ := by
  have hd := Lib.paramCircle_integral_hasFDerivAt38 hVo
    (isolating_radius_pos38 (hf φ hφV) n)
    (moment_joint_boundary_analytic38 V C R hf n k) hφV
  change HasFDerivAt (fun ψ => circleIntegral (momentIntegrand38 ψ k) (C n) (R n))
    (∫ t in Icc 0 (2 * Real.pi), deriv (circleMap (C n) (R n)) t •
      k4aMomentPartial38 φ k (circleMap (C n) (R n) t)) φ at hd
  rw [← circleIntegral_def_Icc (k4aMomentPartial38 φ k) (C n) (R n)] at hd
  exact hd.const_mul (2 * (Real.pi : ℂ) * Complex.I)⁻¹

theorem k4aCircleIntegral_partial_apply38 (φ h : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) (k : ℕ) :
    (circleIntegral (k4aMomentPartial38 φ k) (C n) (R n)) h =
      2 * circleIntegral (fun z => z ^ k * deriv (k4aDirectionQuotient38 φ h) z)
        (C n) (R n) := by
  have hi := k4aMomentPartial_circleIntegrable38 φ k C R hf n
  rw [← circleIntegral.integral_const_mul]
  unfold circleIntegral
  rw [ContinuousLinearMap.intervalIntegral_apply hi.out h]
  apply intervalIntegral.integral_congr
  intro θ _
  have hz := circleMap_mem_sphere (C n) (isolating_radius_pos38 hf n).le θ
  have he := k4aMomentIntegrand_parameter_derivative38 φ h
    (circleMap (C n) (R n) θ) k (isolating_periodic_boundary38 hf n _ hz)
  change deriv (circleMap (C n) (R n)) θ *
      k4aMomentPartial38 φ k (circleMap (C n) (R n) θ) h = _
  rw [show k4aMomentPartial38 φ k (circleMap (C n) (R n) θ) h =
    2 * (circleMap (C n) (R n) θ) ^ k *
      deriv (k4aDirectionQuotient38 φ h) (circleMap (C n) (R n) θ) from he]
  ring

theorem k4aCircleIntegral_quotient_apply38 (φ h : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    (circleIntegral (k4aQuotientCLM38 φ) (C n) (R n)) h =
      circleIntegral (k4aDirectionQuotient38 φ h) (C n) (R n) := by
  have hi := k4aQuotientCLM_circleIntegrable38 φ C R hf n
  unfold circleIntegral
  rw [ContinuousLinearMap.intervalIntegral_apply hi.out h]
  apply intervalIntegral.integral_congr
  intro θ _
  change deriv (circleMap (C n) (R n)) θ *
      ((discrim φ (circleMap (C n) (R n) θ) / perChar φ (circleMap (C n) (R n) θ)) *
        gradDiscrimCLM φ (circleMap (C n) (R n) θ) h) =
    deriv (circleMap (C n) (R n)) θ *
      (discrim φ (circleMap (C n) (R n) θ) *
        gradDiscrimCLM φ (circleMap (C n) (R n) θ) h / perChar φ (circleMap (C n) (R n) θ))
  ring

end
end NlsGge.GK38
