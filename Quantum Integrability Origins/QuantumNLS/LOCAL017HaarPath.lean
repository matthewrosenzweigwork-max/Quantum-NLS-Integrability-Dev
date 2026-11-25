import QuantumNLS.Ext025B7LocalPath
import QuantumNLS.Ext025B10LocalBeta
import QuantumNLS.Ext025B6TorusCoordinates
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! LOCAL-017 item 3: the literal scalar Haar path average.  All parameter
regularity below is for fixed vectors; no operator topology on the torus is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Set Metric Filter Topology
namespace QuantumNLS.LOCAL017Haar
open Ext025B7LocalPath Ext025BHaar
abbrev Cov := H →L[ℝ] ℝ
abbrev Torus := ℤ → Circle

/-- Principal angles, chosen in the closed source cube.  The seam has Haar
measure zero; using the principal branch fixes a measurable representative. -/
def angleLift (ψ : Torus) : AngleBox := fun n =>
  ⟨Complex.arg (ψ n), (Complex.abs_arg_le_pi _ |> abs_le.mp)⟩

theorem angleLift_measurable : Measurable angleLift := by
  apply Measurable.of_eval
  intro n
  exact (Complex.measurable_arg.comp
    (measurable_subtype_coe.comp (measurable_pi_apply n))).subtype_mk

def pathLift (p : Torus × unitInterval) : PathParameter := (angleLift p.1, p.2)

theorem pathLift_measurable : Measurable pathLift :=
  (angleLift_measurable.comp measurable_fst).prodMk measurable_snd

/-- Haar in the angles, normalized Lebesgue measure on the unit time interval. -/
def pathMeasure : Measure PathParameter :=
  (productCircleHaar.prod (volume : Measure unitInterval)).map pathLift

instance : IsProbabilityMeasure pathMeasure :=
  Measure.isProbabilityMeasure_map_iff pathLift_measurable.aemeasurable |>.2 inferInstance

/-- The negative sign is the sign in eq:reset-haar-primitive. -/
def primitive (β : H → Cov) (z : H) : ℝ :=
  -∫ p, pathIntegrand β z p ∂pathMeasure

/-- The actual source radial primitive, without an independent beta field. -/
def sourcePrimitive (Ω : H → Ext025B10LocalBeta.TwoForm)
    (ω : Ext025B10LocalBeta.TwoForm) : H → ℝ :=
  primitive (Ext025B10LocalBeta.sourceBeta Ω ω)

theorem rotation_mem {R : ℝ} {z : H} (hz : z ∈ ball 0 R) (p : PathParameter) :
    rotation p z ∈ ball 0 R := by
  simpa only [mem_ball_zero_iff, rotation_norm] using hz

theorem path_continuousOn {R : ℝ} (β : H → Cov)
    (hβ : ContinuousOn β (ball 0 R)) {z : H} (hz : z ∈ ball 0 R) :
    Continuous (pathIntegrand β z) := by
  have hr : Continuous (fun p : PathParameter => rotation p z) :=
    rotation_continuous.comp (continuous_id.prodMk continuous_const)
  exact (hβ.comp_continuous hr (rotation_mem hz)).clm_apply
    (velocity_continuous.comp (continuous_fst.prodMk hr))

theorem path_integrable {R : ℝ} (β : H → Cov)
    (hβ : ContinuousOn β (ball 0 R)) {z : H} (hz : z ∈ ball 0 R) :
    Integrable (pathIntegrand β z) pathMeasure := by
  simpa using (path_continuousOn β hβ hz).continuousOn.integrableOn_compact
    (μ := pathMeasure) isCompact_univ

/-- Precisely the scalar Haar integral in the principal-angle representation. -/
theorem primitive_haar {R : ℝ} (β : H → Cov)
    (hβ : ContinuousOn β (ball 0 R)) {z : H} (hz : z ∈ ball 0 R) :
    primitive β z = -∫ ψ, ∫ t : unitInterval,
      β (rotation (angleLift ψ, t) z)
        (velocity (angleLift ψ) (rotation (angleLift ψ, t) z))
      ∂volume ∂productCircleHaar := by
  unfold primitive
  congr 1
  rw [pathMeasure, integral_map pathLift_measurable.aemeasurable
    (path_continuousOn β hβ hz).measurable.aestronglyMeasurable]
  exact integral_prod _ ((path_integrable β hβ hz).comp_measurable
    pathLift_measurable)

theorem path_bound {R C : ℝ} (β : H → Cov)
    (hb : ∀ z ∈ ball (0 : H) R, ‖β z‖ ≤ C * ‖z‖^3)
    {z : H} (hz : z ∈ ball 0 R) (p : PathParameter) :
    ‖pathIntegrand β z p‖ ≤ C * Real.pi * ‖z‖^4 := by
  calc
    _ ≤ ‖β (rotation p z)‖ * ‖velocity p.1 (rotation p z)‖ :=
      (β _).le_opNorm _
    _ ≤ (C * ‖rotation p z‖^3) * (Real.pi * ‖rotation p z‖) :=
      mul_le_mul (hb _ (rotation_mem hz p)) (velocity_norm_le _ _)
        (norm_nonneg _) ((norm_nonneg _).trans (hb _ (rotation_mem hz p)))
    _ = _ := by rw [rotation_norm]; ring

theorem primitive_bound {R C : ℝ} (β : H → Cov)
    (hb : ∀ z ∈ ball (0 : H) R, ‖β z‖ ≤ C * ‖z‖^3)
    {z : H} (hz : z ∈ ball 0 R) :
    |primitive β z| ≤ C * Real.pi * ‖z‖^4 := by
  rw [← Real.norm_eq_abs, primitive, norm_neg]
  simpa using norm_integral_le_of_norm_le_const (μ := pathMeasure)
    (Filter.Eventually.of_forall (path_bound β hb hz))

/-- Joint continuity in the base point and compact path parameters. -/
theorem joint_path_continuousOn {R : ℝ} (β : H → Cov)
    (hβ : ContinuousOn β (ball 0 R)) :
    ContinuousOn (fun q : H × PathParameter => pathIntegrand β q.1 q.2)
      (ball 0 R ×ˢ univ) := by
  have hr : Continuous (fun q : H × PathParameter => rotation q.2 q.1) :=
    rotation_continuous.comp (continuous_snd.prodMk continuous_fst)
  have hc : ContinuousOn (fun q : H × PathParameter => β (rotation q.2 q.1))
      (ball 0 R ×ˢ univ) := hβ.comp hr.continuousOn (fun q hq => rotation_mem hq.1 q.2)
  exact hc.clm_apply (velocity_continuous.comp
    ((continuous_fst.comp continuous_snd).prodMk hr)).continuousOn

/-- Continuity of f follows by domination on the original ball. -/
theorem primitive_continuousOn {R C : ℝ} (_hR : 0 < R) (hC : 0 ≤ C)
    (β : H → Cov) (hβ : ContinuousOn β (ball 0 R))
    (hb : ∀ z ∈ ball (0 : H) R, ‖β z‖ ≤ C * ‖z‖^3) :
    ContinuousOn (primitive β) (ball 0 R) := by
  intro z hz
  apply ContinuousWithinAt.neg
  apply continuousWithinAt_of_dominated (bound := fun _ => C * Real.pi * R^4)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (path_continuousOn β hβ hx).measurable.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact .of_forall fun p => (path_bound β hb hx p).trans (by
      gcongr
      exact (mem_ball_zero_iff.mp hx).le)
  · exact integrable_const _
  · apply Eventually.of_forall
    intro p
    have hc : ContinuousWithinAt (fun x : H => (x, p)) (ball 0 R) z :=
      continuousWithinAt_id.prodMk continuousWithinAt_const
    exact ContinuousWithinAt.comp (f := fun x : H => (x,p))
      (joint_path_continuousOn β hβ (z,p) ⟨hz, mem_univ _⟩) hc
      (fun x hx => ⟨hx,mem_univ _⟩)

end QuantumNLS.LOCAL017Haar
