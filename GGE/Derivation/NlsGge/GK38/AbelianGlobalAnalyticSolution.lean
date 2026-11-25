import NlsGge.GK38.AbelianGlobalContinuousSolution
import NlsGge.GK38.AbelianOriginalChartGraph

/-! Uncompiled full global REAL analytic solution construction conditional
ONLY on the literal actual derivative invertibility that parent P4 must
realize. Continuation/covering/fiber cardinality/local branches are earned. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5Continuous_gap_solution_analytic_of_actual_inverse38 (n : ℤ)
    (hQ : ∀ p : p5RealSolutionSpace38 n,
      (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible)
    (σ : C(PhysicalL2,P3RealSpace38 n))
    (hσ : ∀ u : PhysicalL2, σ u ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u (σ u)=0) :
    AnalyticOnNhd ℝ (σ : PhysicalL2 → P3RealSpace38 n) univ := by
  intro u₀ _
  let p : p5RealSolutionSpace38 n := ⟨(u₀,σ u₀),hσ u₀⟩
  obtain ⟨U,V,ψ,hUo,huU,hVo,htV,_hψbase,hψan,hbranch⟩ :=
    p5Actual_local_analytic_gap_graph_of_inverse38 n u₀ (σ u₀)
      (hσ u₀).1 (hσ u₀).2 (hQ p)
  have hσV : ∀ᶠ u in 𝓝 u₀, σ u ∈ V :=
    σ.continuous.continuousAt.preimage_mem_nhds (hVo.mem_nhds htV)
  have he : ψ =ᶠ[𝓝 u₀] σ := by
    filter_upwards [hUo.mem_nhds huU,hσV] with u hu hv
    exact ((hbranch u hu).2.2.2 (σ u) hv).mp (hσ u)
  exact (hψan u₀ huU).congr he

theorem p5Global_analytic_gap_solution_of_actual_inverse38 (n : ℤ)
    (hQ : ∀ p : p5RealSolutionSpace38 n,
      (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible) :
    ∃! σ : PhysicalL2 → P3RealSpace38 n, AnalyticOnNhd ℝ σ univ ∧
      ∀ u : PhysicalL2, σ u ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u (σ u)=0 := by
  obtain ⟨σ,hσ,hunique⟩ := p5Global_continuous_gap_solution_of_actual_inverse38 n hQ
  refine ⟨σ,⟨p5Continuous_gap_solution_analytic_of_actual_inverse38 n hQ σ hσ,hσ⟩,?_⟩
  intro τ hτ
  have hτcont : Continuous τ := continuous_iff_continuousAt.mpr
    (fun u => (hτ.1 u (mem_univ _)).continuousAt)
  have he : (⟨τ,hτcont⟩ : C(PhysicalL2,P3RealSpace38 n))=σ := hunique ⟨τ,hτcont⟩ hτ.2
  funext u
  exact congrArg (fun M : C(PhysicalL2,P3RealSpace38 n) => M u) he

theorem p5Global_analytic_original_chart_solution_of_actual_inverse38 (n : ℤ)
    (hQ : ∀ p : p5RealSolutionSpace38 n,
      (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible) :
    ∃! σ : PhysicalL2 → P3RealSpace38 n, AnalyticOnNhd ℝ σ univ ∧
      ∀ (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ),
        IsolatingFamily38 (realSlice u) C R →
        ∃ s : Lib.L2Seq, (∀ k : ℤ, (s k).im=0) ∧
          p2Restrict38 n s=p3RealInclude38 n (σ u) ∧
          (∀ k : ℤ, Lib.sigmaOf s k ∈ Metric.ball (C k) (R k)) ∧
          p2Fn38 n (realSlice u,p2Restrict38 n s)=0 := by
  obtain ⟨σ,⟨hσan,hσ⟩,hunique⟩ := p5Global_analytic_gap_solution_of_actual_inverse38 n hQ
  refine ⟨σ,⟨hσan,?_⟩,?_⟩
  · intro u C R hfam
    exact (p5Actual_gap_zero_iff_original_full_chart38 n u C R hfam (σ u)).mp (hσ u)
  · intro τ hτ
    apply hunique τ
    refine ⟨hτ.1,?_⟩
    intro u
    let C : ℤ → ℂ := discC (realSlice u)
    let R : ℤ → ℝ := discR (realSlice u)
    have hfam : IsolatingFamily38 (realSlice u) C R :=
      isolating_family38 (realSlice u) (realSlice_mem_gkW u)
    exact (p5Actual_gap_zero_iff_original_full_chart38 n u C R hfam (τ u)).mpr
      (hτ.2 u C R hfam)

end
end NlsGge.GK38
