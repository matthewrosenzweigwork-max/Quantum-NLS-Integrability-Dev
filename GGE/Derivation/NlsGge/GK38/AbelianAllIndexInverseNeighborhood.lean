import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Int.Interval

/-! A signed operator limit and EARNED equicontinuity give one inverse
neighborhood before every index. Individual continuity alone does not suffice.
Actual period-map realization and the final common complex W are separate. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38.P6InverseNeighborhood
noncomputable section

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem all_signed_invertible_eventually
    (T : ℤ → X → E →L[ℂ] E) (S : E →L[ℂ] E) (x : X)
    (hS : S.IsInvertible) (hbase : ∀ n : ℤ, (T n x).IsInvertible)
    (hcont : ∀ n : ℤ, ContinuousAt (T n) x)
    (hlimit : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n : ℤ, (N : ℤ) < |n| → dist (T n x) S < ε)
    (hequi : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y in 𝓝 x, ∀ n : ℤ, dist (T n y) (T n x) < ε) :
    ∀ᶠ y in 𝓝 x, ∀ n : ℤ, (T n y).IsInvertible := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hS.eventually_nhds
  obtain ⟨N,hN⟩ := hlimit (ε/2) (half_pos hε)
  let F : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hfinite : ∀ᶠ y in 𝓝 x, ∀ n ∈ F, (T n y).IsInvertible := by
    apply (F.eventually_all).mpr
    intro n _hn
    exact (hcont n) (hbase n).eventually_nhds
  filter_upwards [hfinite,hequi (ε/2) (half_pos hε)] with y hy he n
  by_cases hn : (N : ℤ) < |n|
  · apply hball
    apply mem_ball.mpr
    have htri := dist_triangle (T n y) (T n x) S
    have hfirst := he n
    have hsecond := hN n hn
    linarith
  · exact hy n (by simpa only [F,Finset.mem_Icc] using abs_le.mp (le_of_not_gt hn))

end
end NlsGge.GK38.P6InverseNeighborhood
