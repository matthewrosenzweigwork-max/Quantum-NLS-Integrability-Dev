import Mathlib
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G6.Energy031A
import NlsGge.ThirdConsultation.G6.Energy031B
import NlsGge.ThirdConsultation.G6.Energy031C

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.HierarchyRiccati.Core

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

namespace NlsGge.GKDefinitionDesign

theorem analyticOnNhd_norm_sq_complex (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    AnalyticOnNhd ℝ (fun x : E => ‖x‖ ^ 2) univ := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  intro x _
  have h : (fun x : E => ‖x‖ ^ 2) = fun x => (innerSL ℝ x : E →L[ℝ] ℝ) x := by
    funext y
    simp [real_inner_self_eq_norm_sq]
  rw [h]
  have h1 := ContinuousLinearMap.analyticAt_bilinear (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) (x, x)
  have h2 : AnalyticAt ℝ (fun y : E => (y, y)) x :=
    AnalyticAt.prod analyticAt_id analyticAt_id
  exact AnalyticAt.comp (f := fun y : E => (y, y)) (g := fun p : E × E => (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) p.1 p.2) h1 h2

def derivCLM : PhysicalSobolev38 ((1 : ℕ) : ℝ) →L[ℝ] PhysicalL2 :=
  ((liftCLM38 (riccatiSobolevIteratedDerivativeL2CLMRecovery30First 1 1 le_rfl)).comp
    (reflCLM ((1 : ℕ) : ℝ))).comp
    (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap

theorem derivCLM_apply (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    derivCLM u = physicalSobolevDerivative38 1 u := rfl

theorem analytic_quad :
    AnalyticOnNhd ℝ (fun u : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
      ‖physicalSobolevDerivative38 1 u‖ ^ 2) univ := by
  intro u hu
  have h := analyticOnNhd_norm_sq_complex PhysicalL2 (derivCLM u) (mem_univ _)
  exact h.comp (derivCLM.analyticAt u)

def integralCLM031 : C(PhysicalCircle, ℝ) →L[ℝ] ℝ :=
  (({ toFun := fun f => ∫ x, f x ∂spatialMeasure
      map_add' := fun f g => integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => by simp [integral_const_mul, smul_eq_mul] } :
      C(PhysicalCircle, ℝ) →ₗ[ℝ] ℝ).mkContinuous 1 (fun f => by
    have := norm_integral_le_of_norm_le_const (μ := spatialMeasure) (f := fun x => f x)
      (C := ‖f‖) (Filter.Eventually.of_forall (fun x => by
        simpa using ContinuousMap.norm_coe_le_norm f x))
    simpa using this))

theorem integralCLM031_apply (f : C(PhysicalCircle, ℝ)) :
    integralCLM031 f = ∫ x, f x ∂spatialMeasure := rfl

theorem analytic_quart :
    AnalyticOnNhd ℝ (fun u : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
      ∫ x : PhysicalCircle, ‖iotaCLM u x‖ ^ 4 ∂spatialMeasure) univ := by
  intro u hu
  let A : PhysicalSobolev38 ((1 : ℕ) : ℝ) →L[ℝ] C(PhysicalCircle, ℝ) :=
    (ContinuousLinearMap.compLeftContinuous ℝ PhysicalCircle Complex.reCLM).comp iotaCLM
  let B : PhysicalSobolev38 ((1 : ℕ) : ℝ) →L[ℝ] C(PhysicalCircle, ℝ) :=
    (ContinuousLinearMap.compLeftContinuous ℝ PhysicalCircle Complex.imCLM).comp iotaCLM
  have hA : AnalyticAt ℝ (fun v => A v) u := A.analyticAt u
  have hB : AnalyticAt ℝ (fun v => B v) u := B.analyticAt u
  have hw : AnalyticAt ℝ (fun v => A v * A v + B v * B v) u := (hA.mul hA).add (hB.mul hB)
  have hg : AnalyticAt ℝ (fun v => integralCLM031 ((A v * A v + B v * B v) *
      (A v * A v + B v * B v))) u := (integralCLM031.analyticAt _).comp (hw.mul hw)
  convert hg using 2 with v
  rw [integralCLM031_apply]
  congr 1
  funext x
  simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, A, B,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compLeftContinuous_apply]
  rw [show ‖iotaCLM v x‖ ^ 4 = (‖iotaCLM v x‖ ^ 2) * (‖iotaCLM v x‖ ^ 2) by ring,
    Complex.sq_norm, Complex.normSq_apply]
  simp

end NlsGge.GKDefinitionDesign
end
