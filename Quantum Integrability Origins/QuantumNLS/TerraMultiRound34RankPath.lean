import QuantumNLS.TerraMultiRound32LocalRank
import Mathlib.Topology.LocallyConstant.Basic

/-! Rank propagation along a continuous idempotent family, starting at the
actual free projection. This is a conditional functional-analytic bridge;
the arbitrary-field Riesz family and its continuity are not constructed here. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
namespace QuantumNLS.TerraMultiRound34RankPath
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Free

/-- A continuous family of idempotents has constant rank two on a connected
parameter space once one member has rank two. -/
theorem rank_two_of_continuous_family {L : ℝ} {X : Type*}
    [TopologicalSpace X] [PreconnectedSpace X]
    (P : X → H2 L →L[ℂ] H2 L) (hc : Continuous P)
    (hi : ∀ x, P x ∘L P x = P x) (x₀ : X)
    (hbase : Module.finrank ℂ (rng (P x₀)) = 2) :
    ∀ x, Module.finrank ℂ (rng (P x)) = 2 := by
  classical
  have hloc : IsLocallyConstant (fun x => Module.finrank ℂ (rng (P x)) = 2) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    have hnear : ∀ᶠ y in 𝓝 x, ‖P y - P x‖ < 1 := by
      have h := hc.continuousAt (x := x) (Metric.ball_mem_nhds (P x) zero_lt_one)
      filter_upwards [h] with y hy
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    filter_upwards [hnear] with y hy
    apply propext
    constructor
    · intro hy2
      have hf : Module.Finite ℂ (rng (P y)) :=
        Module.finite_of_finrank_pos (by rw [hy2]; norm_num)
      have he := (finrank_range_eq_of_close (hi x) (hi y) (by simpa [norm_sub_rev] using hy) hf).2
      rw [he, hy2]
    · intro hx2
      have hf : Module.Finite ℂ (rng (P x)) :=
        Module.finite_of_finrank_pos (by rw [hx2]; norm_num)
      have he := (finrank_range_eq_of_close (hi y) (hi x) hy hf).2
      rw [he, hx2]
  intro x
  have he := hloc.apply_eq_of_preconnectedSpace x x₀
  exact he.mpr hbase

/-- The base rank used in the LOCAL-003 route is that of the actual free
contour projection. The path hypotheses remain obligations for its application. -/
theorem rank_two_from_actual_free {L κ r : ℝ} (hL : 0 < L)
    (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (P : X → H2 L →L[ℂ] H2 L) (hc : Continuous P)
    (hi : ∀ x, P x ∘L P x = P x) (x₀ : X)
    (hbase : P x₀ = freeProj L κ n r) :
    ∀ x, Module.finrank ℂ (rng (P x)) = 2 := by
  apply rank_two_of_continuous_family P hc hi x₀
  rw [hbase]
  exact (QuantumNLS.TerraMultiRound32LocalRank.actual_base_and_nearby_rank_two
    (κ := κ) hL hr hr2).1 n

end QuantumNLS.TerraMultiRound34RankPath
#print axioms QuantumNLS.TerraMultiRound34RankPath.rank_two_of_continuous_family
#print axioms QuantumNLS.TerraMultiRound34RankPath.rank_two_from_actual_free
