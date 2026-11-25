import NlsGge.GK38.AbelianNormalizedCommonInverseBranches
import NlsGge.GK38.AbelianNormalizedOverlapAgreement
import NlsGge.GK38.AbelianAnalyticUnionGluing
import NlsGge.GK38.IsolatingTopology

/-! Actual normalized omitted solutions extend to ONE complex neighborhood
of the full real L2 slice before ALL signed labels. Real-trace rigidity and
actual complex local uniqueness earn overlap agreement before analytic gluing.
No global branch, continuation or inverse oracle is a premise. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6Actual_common_complex_normalized_inverse_neighborhood38 :
    ∃ W : Set PotPair, IsOpen W ∧ range realSlice ⊆ W ∧ W ⊆ gkW ∧
      ∀ n : ℤ, ∃ F : PotPair → P2Space38 n, AnalyticOnNhd ℂ F W ∧
        (∀ φ ∈ W, p2Fn38 n (φ,F φ)=0 ∧
          (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (φ,y)) (F φ)).IsInvertible) ∧
        ∀ u : PhysicalL2, ∃ t : P3RealSpace38 n,
          t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0 ∧
          F (realSlice u)=p3RealInclude38 n t := by
  classical
  choose C R hfam using fun u : PhysicalL2 =>
    exists_isolating_family38 (realSlice u) (realSlice_mem_gkW u)
  choose δ B hδ hB hW hbranches using fun u : PhysicalL2 =>
    p6Normalized_common_complex_inverse_branches38 u (C u) (R u) (hfam u)
  choose t ht htz S hbase han hspec using hbranches
  let U : PhysicalL2 → Set PotPair := fun u => ball (realSlice u) (δ u)
  have htrace (u : PhysicalL2) (n : ℤ) :
      ∃ σ : PhysicalL2 → P3RealSpace38 n, AnalyticOnNhd ℝ σ univ ∧
        (∀ v, σ v ∈ p5RealGapCube38 n v ∧ p3RealFn38 n v (σ v)=0) ∧
        ∀ v ∈ ball u (δ u),
          p2Restrict38 n (S u n (realSlice v))=p3RealInclude38 n (σ v) := by
    apply p6Normalized_zero_branch_agrees_on_real_trace38 n u (δ u) (hδ u) (hW u)
      (S u n) (han u n).continuousOn
      (fun φ hφ => (hspec u n φ hφ).1)
      (fun φ hφ => (hspec u n φ hφ).2.2.2.2) (t u n) (ht u n) (htz u n)
    rw [hbase u n,p6GapCubeComplete_restrict38]
  choose σ hσan hσspec hreal using htrace
  let W : Set PotPair := ⋃ u, U u
  have hWU : W ⊆ gkW := by
    intro φ hφ
    obtain ⟨u,hu⟩ := mem_iUnion.mp hφ
    exact hW u hu
  refine ⟨W,isOpen_iUnion (fun _ => isOpen_ball),?_,hWU,?_⟩
  · rintro φ ⟨u,rfl⟩
    exact mem_iUnion.mpr ⟨u,mem_ball_self (hδ u)⟩
  · intro n
    let f : PhysicalL2 → PotPair → P2Space38 n := fun u φ => p2Restrict38 n (S u n φ)
    have hfa (u : PhysicalL2) : AnalyticOnNhd ℂ (f u) (U u) := by
      intro φ hφ
      exact AnalyticAt.comp (g := p2Restrict38 n) (f := S u n)
        ((p2Restrict38 n).analyticAt _) (han u n φ hφ)
    have hcompat (u v : PhysicalL2) (φ : PotPair) (hu : φ ∈ U u) (hv : φ ∈ U v) :
        f u φ=f v φ := by
      apply p6Omitted_normalized_complex_ball_overlap_agreement38 n u v (δ u) (δ v)
        (S u n) (S v n) (han u n).continuousOn (han v n).continuousOn (hW u)
        (fun q hq => (hspec u n q hq).1) (fun q hq => (hspec v n q hq).1)
        (fun q hq => (hspec u n q hq).2.2.2.2)
        (σ u n) (σ v n) (hσspec u n) (hσspec v n)
        (fun w hw => hreal u n w (by simpa only [mem_ball,dist_realSlice] using hw))
        (fun w hw => hreal v n w (by simpa only [mem_ball,dist_realSlice] using hw)) φ ⟨hu,hv⟩
    obtain ⟨F,hFa,hFeq⟩ := P6AnalyticGluing.exists_analytic_eqOn_open_union U
      (fun _ => isOpen_ball) f hfa hcompat
    refine ⟨F,hFa,?_,?_⟩
    · intro φ hφ
      obtain ⟨u,hu⟩ := mem_iUnion.mp hφ
      rw [hFeq u hu]
      exact ⟨(hspec u n φ hu).1,(hspec u n φ hu).2.2.2.2⟩
    · intro u
      refine ⟨t u n,ht u n,htz u n,?_⟩
      rw [hFeq u (mem_ball_self (hδ u))]
      change p2Restrict38 n (S u n (realSlice u))=p3RealInclude38 n (t u n)
      rw [hbase u n,p6GapCubeComplete_restrict38]

end
end NlsGge.GK38
