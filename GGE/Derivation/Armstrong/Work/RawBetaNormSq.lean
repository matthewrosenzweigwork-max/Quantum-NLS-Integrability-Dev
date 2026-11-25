import Mathlib.Analysis.Complex.BranchLogRoot

set_option autoImplicit false
open Filter Topology
namespace NlsGge.GK38

theorem rawBetaTendstoZeroOfNormSq38
    {α : Type*} [TopologicalSpace α] {l : Filter α} {f : α → ℂ}
    (hf : Tendsto (fun x => ‖f x‖ ^ 2) l (𝓝 (0 : ℝ))) :
    Tendsto f l (𝓝 (0 : ℂ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsq := (Metric.tendsto_nhds.mp hf) (ε ^ 2) (sq_pos_of_pos hε)
  filter_upwards [hsq] with x hx
  have hx' : ‖f x‖ ^ 2 < ε ^ 2 := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (sq_nonneg (‖f x‖))] using hx
  rw [dist_eq_norm, sub_zero]
  nlinarith [norm_nonneg (f x), hε]

end NlsGge.GK38

#check @NlsGge.GK38.rawBetaTendstoZeroOfNormSq38
#print axioms NlsGge.GK38.rawBetaTendstoZeroOfNormSq38
