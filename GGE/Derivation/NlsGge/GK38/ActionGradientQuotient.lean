import NlsGge.GK38.ContourAction
import NlsGge.GK38.TauGammaCircleMoments
import NlsGge.GK38.GradFundamentalGradient
import NlsGge.GK38.Lib.ParamCircleAnalytic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.Pilot
namespace NlsGge.GK38.ActionGradient
noncomputable section

theorem gradDiscrim_eq_partial (φ : PotPair) (z : ℂ) :
    gradDiscrimCLM φ z =
      (fderiv ℂ (fun p : PotPair × ℂ => discrim p.1 p.2) (φ, z)).comp
        (ContinuousLinearMap.inl ℂ PotPair ℂ) := by
  have hd := NlsGge.GK38.Lib.paramCircle_hasFDerivAt38
    (F := fun ψ w => discrim ψ w) (analyticOnNhd_discrim (φ, z) (mem_univ _))
  exact (hasFDerivAt_gradDiscrimCLM φ z).unique hd

theorem gradDiscrim_joint_analytic :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => gradDiscrimCLM p.1 p.2) univ := by
  let F : PotPair × ℂ → ℂ := fun p => discrim p.1 p.2
  let T : ((PotPair × ℂ) →L[ℂ] ℂ) →L[ℂ] (PotPair →L[ℂ] ℂ) :=
    (ContinuousLinearMap.compL ℂ PotPair (PotPair × ℂ) ℂ).flip
      (ContinuousLinearMap.inl ℂ PotPair ℂ)
  have he : (fun p : PotPair × ℂ => T (fderiv ℂ F p)) =
      (fun p : PotPair × ℂ => gradDiscrimCLM p.1 p.2) := by
    funext p
    exact (gradDiscrim_eq_partial p.1 p.2).symm
  rw [← he]
  intro p hp
  exact (T.analyticAt _).comp ((analyticOnNhd_discrim p hp).fderiv)

def gradRootQuotient (φ : PotPair) (z : ℂ) : PotPair →L[ℂ] ℂ :=
  (canonRoot38 φ z)⁻¹ • gradDiscrimCLM φ z

theorem gradRootQuotient_joint_analytic :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => gradRootQuotient p.1 p.2) rootDomain38 := by
  intro p hp
  exact ((canonRoot_analytic38 p hp).inv
    (canonRoot_ne_zero38 p.1 hp.1 p.2 hp.2)).smul (gradDiscrim_joint_analytic p (mem_univ _))

theorem gradRootQuotient_fibre_analytic (φ : PotPair) (hφ : φ ∈ gkW) :
    AnalyticOnNhd ℂ (gradRootQuotient φ) (actionCutDomain38 φ) := by
  intro z hz
  exact (gradRootQuotient_joint_analytic (φ, z) ⟨hφ, hz⟩).comp
    ((analyticAt_const (v := φ)).prod analyticAt_id)

theorem gradRootQuotient_circle_integrable (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (gradRootQuotient φ) (C n) (R n) := by
  have hs := fixed_sphere_subset φ C R hf n
  exact ((gradRootQuotient_fibre_analytic φ hφ).continuousOn.mono hs).circleIntegrable
    (isolating_radius_pos38 hf n).le

theorem gradRootQuotient_direction_circle_integrable (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) (h : PotPair) :
    CircleIntegrable (fun z => gradDiscrimCLM φ z h / canonRoot38 φ z) (C n) (R n) := by
  let ev : (PotPair →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ h
  have ha : AnalyticOnNhd ℂ (fun z => ev (gradRootQuotient φ z)) (actionCutDomain38 φ) := by
    intro z hz
    exact (ev.analyticAt _).comp (gradRootQuotient_fibre_analytic φ hφ z hz)
  have hi := (ha.continuousOn.mono (fixed_sphere_subset φ C R hf n)).circleIntegrable
    (isolating_radius_pos38 hf n).le
  change CircleIntegrable (fun z => (canonRoot38 φ z)⁻¹ * gradDiscrimCLM φ z h)
    (C n) (R n) at hi
  simpa only [div_eq_mul_inv, mul_comm] using hi

def actionGradientCLM38 (φ : PotPair) (n : ℤ) : PotPair →L[ℂ] ℂ :=
  -(1 / (Real.pi : ℂ)) • circleIntegral (gradRootQuotient φ) (discC φ n) (discR φ n)

theorem actionGradient_integrable (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    CircleIntegrable (gradRootQuotient φ) (discC φ n) (discR φ n) :=
  gradRootQuotient_circle_integrable φ hφ _ _ (isolating_family38 φ hφ) n

end
end NlsGge.GK38.ActionGradient
