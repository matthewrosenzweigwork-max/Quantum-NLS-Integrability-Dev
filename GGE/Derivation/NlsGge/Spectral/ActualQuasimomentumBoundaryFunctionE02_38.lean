import NlsGge.Spectral.ActualQuasimomentumBoundaryLimitE02_38
import NlsGge.Spectral.ActualQuasimomentumFullInfinityE02_38
import NlsGge.Herglotz38.HalfPlaneMinPrincipleLimitsE02_38
import Mathlib.Topology.ExtendFrom
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # Real boundary value `k(x + i0)` of the quasimomentum (campaign 38) -/

/-- The boundary value `k(x + i0) = p(x) + i v(x)` at a real point. -/
def actualQuasimomentumBoundaryE02_38 (u : PhysicalL2) (x : ℝ) : ℂ :=
  extendFrom {z : ℂ | 0 < z.im} (actualQuasimomentumE02_38 u) (x:ℂ)

/-- Source `p(x) = Re k(x + i0)`. -/
def actualQuasimomentumRealPartE02_38 (u : PhysicalL2) (x : ℝ) : ℝ :=
  (actualQuasimomentumBoundaryE02_38 u x).re

theorem tendsto_actualQuasimomentumBoundaryE02_38 (u : PhysicalL2) (x : ℝ) :
    Tendsto (actualQuasimomentumE02_38 u) (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ))
      (𝓝 (actualQuasimomentumBoundaryE02_38 u x)) := by
  obtain ⟨L, hL, -⟩ := exists_tendsto_actualQuasimomentum_boundary_E02_38 u x
  exact tendsto_extendFrom ⟨L, hL⟩

theorem continuousOn_extend_actualQuasimomentumE02_38 (u : PhysicalL2) :
    ContinuousOn (extendFrom {z : ℂ | 0 < z.im} (actualQuasimomentumE02_38 u))
      {z : ℂ | 0 ≤ z.im} := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  have hUo : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  apply continuousOn_extendFrom (fun x hx => mem_closure_upperHalfPlane_E02_38 hx)
  intro x hx
  rcases lt_or_eq_of_le (show (0:ℝ) ≤ x.im from hx) with hpos | hzero
  · refine ⟨actualQuasimomentumE02_38 u x, ?_⟩
    have := (hk.1.continuousOn x hpos).tendsto
    rwa [nhdsWithin_eq_nhds.mpr (hUo.mem_nhds hpos)] at this ⊢
  · have hxr : x = ((x.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hzero])
    obtain ⟨L, hL, -⟩ := exists_tendsto_actualQuasimomentum_boundary_E02_38 u x.re
    exact ⟨L, by rw [hxr]; exact hL⟩

theorem continuous_actualQuasimomentumBoundaryE02_38 (u : PhysicalL2) :
    Continuous (actualQuasimomentumBoundaryE02_38 u) := by
  have h := continuousOn_extend_actualQuasimomentumE02_38 u
  exact h.comp_continuous Complex.continuous_ofReal (fun x => by simp)

theorem continuous_actualQuasimomentumRealPartE02_38 (u : PhysicalL2) :
    Continuous (actualQuasimomentumRealPartE02_38 u) :=
  Complex.continuous_re.comp (continuous_actualQuasimomentumBoundaryE02_38 u)

theorem actualQuasimomentumBoundaryE02_38_cos (u : PhysicalL2) (x : ℝ) :
    Complex.cos (actualQuasimomentumBoundaryE02_38 u x) = actualPhysicalUnitHalfTrace32 u x := by
  obtain ⟨L, hL, hcos, -⟩ := exists_tendsto_actualQuasimomentum_boundary_E02_38 u x
  have : (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_upperHalfPlane_E02_38 (by simp))
  rw [tendsto_nhds_unique (tendsto_actualQuasimomentumBoundaryE02_38 u x) hL, hcos]

/-- `p(x) - x → 0` as `|x| → ∞` (uniformly: `|k(x+i0) - x| ≤ ε` for `|x| ≥ R`). -/
theorem actualQuasimomentumBoundaryE02_38_sub_le (u : PhysicalL2) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, R ≤ |x| →
      ‖actualQuasimomentumBoundaryE02_38 u x - x‖ ≤ ε := by
  intro ε hε
  obtain ⟨R, hR, hb⟩ := actualQuasimomentumE02_38_sub_tendsto_zero u ε hε
  refine ⟨R + 1, by linarith, fun x hx => ?_⟩
  have : (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_upperHalfPlane_E02_38 (by simp))
  have hlim := ((tendsto_actualQuasimomentumBoundaryE02_38 u x).sub
    (tendsto_id.mono_left nhdsWithin_le_nhds)).norm
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (x:ℂ) one_pos)] with z hz hzb
  apply (hb z hz _).le
  have h1 : ‖(x:ℂ)‖ ≤ ‖z‖ + ‖(x:ℂ) - z‖ := by
    have := norm_add_le z ((x:ℂ) - z); simpa using this
  have h2 : ‖(x:ℂ) - z‖ < 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hzb; rwa [norm_sub_rev]
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  linarith

end NlsGge.SpectralFoundations
end
