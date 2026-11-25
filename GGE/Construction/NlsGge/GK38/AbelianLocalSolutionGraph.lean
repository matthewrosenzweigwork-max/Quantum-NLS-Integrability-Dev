import NlsGge.GK38.AbelianLocalAnalyticImplicit
import NlsGge.GK38.AbelianLocalGapZeros

/-! Uncompiled actual local analytic GRAPH in the real closed-gap solution
space. The literal actual hQ is the explicit parent-P4 realization obligation.
The gap-graph conclusions are earned, not assumed as local-chart hypotheses. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5Actual_local_analytic_gap_graph_of_inverse38 (n : ℤ)
    (u₀ : PhysicalL2) (t₀ : P3RealSpace38 n)
    (ht₀ : t₀ ∈ p5RealGapCube38 n u₀) (hzero : p3RealFn38 n u₀ t₀=0)
    (hQ : (fderiv ℝ (p3RealFn38 n u₀) t₀).IsInvertible) :
    ∃ (U : Set PhysicalL2) (V : Set (P3RealSpace38 n)) (ψ : PhysicalL2 → P3RealSpace38 n),
      IsOpen U ∧ u₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧ ψ u₀=t₀ ∧ AnalyticOnNhd ℝ ψ U ∧
      ∀ u ∈ U, ψ u ∈ V ∧ ψ u ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u (ψ u)=0 ∧
        ∀ t ∈ V, (t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0) ↔ ψ u=t := by
  obtain ⟨ψ,hψbase,hψan,hψzero,hψiff⟩ :=
    p5Actual_local_analytic_implicit_of_actual_inverse38 n u₀ t₀ hzero hQ
  obtain ⟨W,hW,hWgap⟩ := p5Near_real_zero_in_actual_gaps38 n u₀ t₀ ht₀
  have hcommon : {p : PhysicalL2 × P3RealSpace38 n |
      (p3RealFn38 n p.1 p.2=0 ↔ ψ p.1=p.2) ∧
      (p3RealFn38 n p.1 p.2=0 → p.2 ∈ p5RealGapCube38 n p.1)} ∈ 𝓝 (u₀,t₀) := by
    filter_upwards [hψiff,hW] with p hp hWp
    exact ⟨hp,hWgap p hWp⟩
  obtain ⟨A,B,hAo,huA,hBo,htB,hAB⟩ := mem_nhds_prod_iff'.mp hcommon
  have hψB : ∀ᶠ u in 𝓝 u₀, ψ u ∈ B :=
    hψan.continuousAt.preimage_mem_nhds (by simpa only [hψbase] using hBo.mem_nhds htB)
  have hnear : {u : PhysicalL2 | u ∈ A ∧ ψ u ∈ B ∧ AnalyticAt ℝ ψ u ∧
      p3RealFn38 n u (ψ u)=0} ∈ 𝓝 u₀ := by
    filter_upwards [hAo.mem_nhds huA,hψB,hψan.eventually_analyticAt,hψzero] with u hu hB ha hz
    exact ⟨hu,hB,ha,hz⟩
  obtain ⟨U,hUsub,hUo,huU⟩ := mem_nhds_iff.mp hnear
  refine ⟨U,B,ψ,hUo,huU,hBo,htB,hψbase,(fun u hu => (hUsub hu).2.2.1),?_⟩
  intro u hu
  obtain ⟨huA,hψBu,hψAu,hψZu⟩ := hUsub hu
  have hgap := (hAB (show (u,ψ u) ∈ A ×ˢ B from ⟨huA,hψBu⟩)).2 hψZu
  refine ⟨hψBu,hgap,hψZu,?_⟩
  intro t ht
  constructor
  · intro hsol
    exact (hAB (show (u,t) ∈ A ×ˢ B from ⟨huA,ht⟩)).1.mp hsol.2
  · intro he
    rw [← he]
    exact ⟨hgap,hψZu⟩

end
end NlsGge.GK38
