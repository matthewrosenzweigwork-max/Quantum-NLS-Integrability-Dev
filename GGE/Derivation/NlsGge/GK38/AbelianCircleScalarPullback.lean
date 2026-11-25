import NlsGge.GK38.AbelianQuarterArcGeometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! SOURCE ONLY: actual wholecircle scalar density and all-angle continuity.
CircleCI and scalarCI precede the parameter identity; exact periodicity will
allow the four actual quarter arcs to telescope over a shifted fullturn.
No circle-square identity assumed. Exact targets+English preceded proof.
UNCOMPILED, outside prospective sectortransport4 scientific scope. -/
set_option autoImplicit false
open Set Metric MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

def p6CirclePullback38 (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ → ℂ :=
  fun θ => f (circleMap c r θ)*(circleMap 0 r θ*Complex.I)

theorem p6Annulus_circle_pullback_continuous38 (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (p6SquareAnnulus38 c r)) :
    Continuous (p6CirclePullback38 f c r) := by
  have htrace (θ : ℝ) : circleMap c r θ ∈ p6SquareAnnulus38 c r := by
    have hn : ‖circleMap c r θ-c‖ = r := by simp [abs_of_nonneg hr]
    refine ⟨hn.ge,?_⟩
    have hre := Complex.abs_re_le_norm (circleMap c r θ-c)
    simpa only [Complex.sub_re,hn] using hre
  have hfcircle : Continuous (fun θ : ℝ => f (circleMap c r θ)) :=
    hf.continuousOn.comp_continuous (continuous_circleMap c r) htrace
  exact hfcircle.mul ((continuous_circleMap 0 r).mul continuous_const)

theorem p6CirclePullback_periodic38 (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    Function.Periodic (p6CirclePullback38 f c r) (2*Real.pi) := by
  intro θ
  simp only [p6CirclePullback38,(periodic_circleMap c r) θ,(periodic_circleMap 0 r) θ]

theorem p6Annulus_circle_integral_param38 (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (p6SquareAnnulus38 c r)) :
    CircleIntegrable f c r ∧
    IntervalIntegrable (p6CirclePullback38 f c r) volume 0 (2*Real.pi) ∧
    circleIntegral f c r = ∫ θ : ℝ in (0 : ℝ)..(2*Real.pi), p6CirclePullback38 f c r θ := by
  refine ⟨p6Annulus_circle_integrable38 c r hr f hf,
    (p6Annulus_circle_pullback_continuous38 c r hr f hf).intervalIntegrable _ _,?_⟩
  rw [circleIntegral]
  apply intervalIntegral.integral_congr
  intro θ hθ
  change deriv (circleMap c r) θ • f (circleMap c r θ) = p6CirclePullback38 f c r θ
  rw [(hasDerivAt_circleMap c r θ).deriv]
  simp only [p6CirclePullback38,smul_eq_mul,mul_comm]

end
end NlsGge.GK38
