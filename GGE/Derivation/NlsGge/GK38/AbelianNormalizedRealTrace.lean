import NlsGge.GK38.AbelianOmittedZeroContinuation
import NlsGge.GK38.AbelianActualPointwiseSolution
import Mathlib.Analysis.Convex.Topology

/-! A continuous complex normalized zero branch agrees on its entire real
trace with the genuine global real normalized solution. This uses actual
omitted complex local uniqueness on a connected REAL ball, without a complex
identity principle or an assumed real-valued complex selection. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6Normalized_zero_branch_agrees_on_real_trace38 (n : ℤ)
    (u : PhysicalL2) (δ : ℝ) (hδ : 0 < δ)
    (hW : ball (realSlice u) δ ⊆ gkW)
    (S : PotPair → Lib.L2Seq) (hS : ContinuousOn S (ball (realSlice u) δ))
    (hz : ∀ φ ∈ ball (realSlice u) δ, p2Fn38 n (φ,p2Restrict38 n (S φ))=0)
    (hinv : ∀ φ ∈ ball (realSlice u) δ,
      (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t))
        (p2Restrict38 n (S φ))).IsInvertible)
    (t₀ : P3RealSpace38 n) (ht₀ : t₀ ∈ p5RealGapCube38 n u)
    (htzero : p3RealFn38 n u t₀=0)
    (hbase : p2Restrict38 n (S (realSlice u))=p3RealInclude38 n t₀) :
    ∃ σ : PhysicalL2 → P3RealSpace38 n, AnalyticOnNhd ℝ σ univ ∧
      (∀ v, σ v ∈ p5RealGapCube38 n v ∧ p3RealFn38 n v (σ v)=0) ∧
      ∀ v ∈ ball u δ,
        p2Restrict38 n (S (realSlice v))=p3RealInclude38 n (σ v) := by
  obtain ⟨σ,⟨hσan,hσspec⟩,_hσunique⟩ := p5Actual_global_analytic_gap_solution38 n
  have hσbase : σ u=t₀ := by
    obtain ⟨a,_ha,hu⟩ := p5Actual_gap_solution_pointwise_unique38 n u
    exact (hu (σ u) (hσspec u)).trans (hu t₀ ⟨ht₀,htzero⟩).symm
  let X : Type := ball u δ
  let : PreconnectedSpace X :=
    isPreconnected_iff_preconnectedSpace.mp (convex_ball u δ).isPreconnected
  let χ : X → PotPair := fun v => realSlice v.val
  have hχ : Continuous χ := continuous_realSlice.comp continuous_subtype_val
  have hχball (v : X) : χ v ∈ ball (realSlice u) δ := by
    simpa only [χ,mem_ball,dist_realSlice] using v.property
  let f : X → P2Space38 n := fun v => p2Restrict38 n (S (χ v))
  let g : X → P2Space38 n := fun v => p3RealInclude38 n (σ v.val)
  have hf : Continuous f := (p2Restrict38 n).continuous.comp
    (hS.comp_continuous hχ hχball)
  have hσcont : Continuous σ := continuous_iff_continuousAt.mpr
    (fun v => (hσan v (mem_univ _)).continuousAt)
  have hg : Continuous g := (p3RealInclude38 n).continuous.comp
    (hσcont.comp continuous_subtype_val)
  have hgzero (v : X) : p2Fn38 n (χ v,g v)=0 := by
    change p2Fn38 n (realSlice v.val,p3RealInclude38 n (σ v.val))=0
    rw [← p3RealFn_graph38,(hσspec v.val).2,map_zero]
  have heq : f=g := p6Omitted_zero_branches_eq_of_continuation38 n χ hχ
    (fun v => hW (hχball v)) f g hf hg
    (fun v => hz (χ v) (hχball v)) hgzero
    (fun v => hinv (χ v) (hχball v)) ⟨u,mem_ball_self hδ⟩
    (by change p2Restrict38 n (S (realSlice u))=p3RealInclude38 n (σ u)
        rw [hbase,hσbase])
  refine ⟨σ,hσan,hσspec,?_⟩
  intro v hv
  exact congrFun heq ⟨v,hv⟩

end
end NlsGge.GK38
