import NlsGge.GK38.Lib.WeaklyAnalytic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! Fixed-circle parameter bounds for D4. Only the spectral circle is compact.
The Banach parameter neighborhood need not be compact or finite dimensional. -/

set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology

namespace NlsGge.GK38.Lib
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The actual partial Fréchet derivative in the parameter direction. -/
def paramCircleDerivative38 (F : E → ℂ → ℂ) (x : E) (z : ℂ) : E →L[ℂ] ℂ :=
  (fderiv ℂ (Function.uncurry F) (x, z)).comp (ContinuousLinearMap.inl ℂ E ℂ)

theorem paramCircle_hasFDerivAt38 {F : E → ℂ → ℂ} {x : E} {z : ℂ}
    (h : AnalyticAt ℂ (Function.uncurry F) (x, z)) :
    HasFDerivAt (fun y => F y z) (paramCircleDerivative38 F x z) x := by
  have hi : HasFDerivAt (fun y : E => (y, z)) (ContinuousLinearMap.inl ℂ E ℂ) x := by
    convert (hasFDerivAt_id x).prodMk (hasFDerivAt_const z x) using 1 <;> ext y <;> rfl
  exact h.differentiableAt.hasFDerivAt.comp x hi

/-- A single small parameter ball controls values, derivatives and analyticity
at every point of the fixed spectral circle. -/
theorem paramCircle_common_bound38 {V : Set E} {c : ℂ} {r : ℝ} {F : E → ℂ → ℂ}
    (hV : IsOpen V) (hF : AnalyticOnNhd ℂ (Function.uncurry F) (V ×ˢ sphere c r))
    {x₀ : E} (hx₀ : x₀ ∈ V) :
    ∃ ε > 0, ∃ B : ℝ, 0 ≤ B ∧ ball x₀ ε ⊆ V ∧
      ∀ x ∈ ball x₀ ε, ∀ z ∈ sphere c r,
        AnalyticAt ℂ (Function.uncurry F) (x, z) ∧ ‖F x z‖ ≤ B ∧
          ‖fderiv ℂ (Function.uncurry F) (x, z)‖ ≤ B := by
  let J := fderiv ℂ (Function.uncurry F)
  have hpair : Continuous (fun z : ℂ => (x₀, z)) := by fun_prop
  have hv : ContinuousOn (F x₀) (sphere c r) := by
    exact hF.continuousOn.comp hpair.continuousOn (fun z hz => ⟨hx₀, hz⟩)
  have hd : ContinuousOn (fun z => J (x₀, z)) (sphere c r) := by
    exact hF.fderiv.continuousOn.comp hpair.continuousOn (fun z hz => ⟨hx₀, hz⟩)
  obtain ⟨A, hA⟩ := (isCompact_sphere c r).exists_bound_of_continuousOn hv
  obtain ⟨D, hD⟩ := (isCompact_sphere c r).exists_bound_of_continuousOn hd
  let B : ℝ := max 0 (max A D) + 1
  have hAB : A + 1 ≤ B := by
    dsimp [B]; gcongr; exact (le_max_left A D).trans (le_max_right 0 (max A D))
  have hDB : D + 1 ≤ B := by
    dsimp [B]; gcongr; exact (le_max_right A D).trans (le_max_right 0 (max A D))
  have hlocal : ∀ z ∈ sphere c r, ∀ᶠ p : E × ℂ in 𝓝 (x₀, z),
      AnalyticAt ℂ (Function.uncurry F) p ∧ ‖F p.1 p.2‖ ≤ B ∧ ‖J p‖ ≤ B := by
    intro z hz
    have ha := hF (x₀, z) ⟨hx₀, hz⟩
    have hev := ha.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one ‖F x₀ z‖))
    have hed := ha.fderiv.continuousAt.norm.eventually
      (gt_mem_nhds (lt_add_one ‖J (x₀, z)‖))
    filter_upwards [ha.eventually_analyticAt, hev, hed] with p hp hpv hpd
    change ‖F p.1 p.2‖ < ‖F x₀ z‖ + 1 at hpv
    change ‖J p‖ < ‖J (x₀, z)‖ + 1 at hpd
    refine ⟨hp, ?_, ?_⟩
    · have := hA z hz; linarith
    · have := hD z hz; linarith
  have hu := (isCompact_sphere c r).eventually_forall_of_forall_eventually
    (P := fun x z => AnalyticAt ℂ (Function.uncurry F) (x, z) ∧
      ‖F x z‖ ≤ B ∧ ‖J (x, z)‖ ≤ B) (by simpa using hlocal)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff_ball.mp (hu.and (hV.mem_nhds hx₀))
  refine ⟨ε, hε, B, ?_, fun x hx => (he x hx).2, ?_⟩
  · dsimp [B]; positivity
  · intro x hx z hz
    exact (he x hx).1 z hz

/-- Continuous boundary values give genuine circle integrability. -/
theorem paramCircle_integrable38 {V : Set E} {c : ℂ} {r : ℝ} {F : E → ℂ → ℂ}
    (hr : 0 < r) (hF : AnalyticOnNhd ℂ (Function.uncurry F) (V ×ˢ sphere c r))
    {x : E} (hx : x ∈ V) : CircleIntegrable (F x) c r := by
  apply ContinuousOn.circleIntegrable hr.le
  exact hF.continuousOn.comp (by fun_prop : ContinuousOn (fun z : ℂ => (x, z)) (sphere c r))
    (fun z hz => ⟨hx, hz⟩)

end
end NlsGge.GK38.Lib
