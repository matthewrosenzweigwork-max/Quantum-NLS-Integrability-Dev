import NlsGge.GK38.EigenvalueCompactnessPhaseLimits
import Mathlib.Topology.Instances.ZMultiples
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Analysis.Normed.Module.Connected

/-! # S7: continuous integer half-turns are constant on connected sets -/
set_option autoImplicit false
open Set Topology
namespace NlsGge.GK38
noncomputable section

theorem continuous_halfturn_constant38 {α : Type*} [TopologicalSpace α] (S : Set α)
    (hS : IsPreconnected S) (f : α → ℝ) (hf : ContinuousOn f S)
    (hZ : ∀ x ∈ S, ∃ m : ℤ, f x = (m : ℝ) * Real.pi)
    {a b : α} (ha : a ∈ S) (hb : b ∈ S) : f a = f b := by
  have hD : IsDiscrete (AddSubgroup.zmultiples Real.pi : Set ℝ) := by
    rw [SetLike.isDiscrete_iff_discreteTopology]
    infer_instance
  apply hS.constant_of_mapsTo hD hf _ ha hb
  intro x hx
  obtain ⟨m, hm⟩ := hZ x hx
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨m, by simpa only [zsmul_eq_mul] using hm.symm⟩

theorem complex_unit_circle_preconnected38 : IsPreconnected (Metric.sphere (0 : ℂ) 1) := by
  apply isPreconnected_sphere
  rw [← Module.finrank_eq_rank]
  norm_num [Complex.finrank_real_complex]

end
end NlsGge.GK38
