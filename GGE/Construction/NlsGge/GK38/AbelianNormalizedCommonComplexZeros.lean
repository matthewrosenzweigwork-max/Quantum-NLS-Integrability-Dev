import NlsGge.GK38.AbelianActualCommonAnalyticLevels
import NlsGge.GK38.AbelianGapCubeCompletion
import NlsGge.GK38.AbelianActualPointwiseSolution

/-! Actual normalized omitted-period zeros on ONE complex neighborhood
before every signed label. Genuine real zeros are completed in the full gap
cube; restriction removes the literal nonzero padded seed level. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6PaddedFn_restrict38 (n : ℤ) (φ : PotPair) (s : Lib.L2Seq) :
    p2Restrict38 n (p6PaddedFn38 n (φ,s))=p2Fn38 n (φ,p2Restrict38 n s) := by
  apply Subtype.ext
  funext m
  simp only [p2Restrict_apply38,p6PaddedFn38,lp.coeFn_add,Pi.add_apply,p2Extend_at38,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (s n) m.property,mul_zero,add_zero]

theorem p6FullGap_common_complex_normalized_zero_branches38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ ball (realSlice u) δ ⊆ gkW ∧
      ∀ n : ℤ, ∃ t : P3RealSpace38 n,
        t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0 ∧
        ∃ S : PotPair → Lib.L2Seq,
          S (realSlice u)=p6RealInclude38 (p6GapCubeComplete38 n u t) ∧
          AnalyticOnNhd ℂ S (ball (realSlice u) δ) ∧
          ∀ φ ∈ ball (realSlice u) δ,
            p2Fn38 n (φ,p2Restrict38 n (S φ))=0 ∧
            ‖S φ-S (realSlice u)‖ ≤ r/2 := by
  obtain ⟨r,δ,hr,hδ,hW,hbranch⟩ :=
    p6FullGap_common_complex_analytic_level_branches38 u C R hfam
  refine ⟨r,δ,hr,hδ,hW,?_⟩
  intro n
  obtain ⟨t,ht,_hUnique⟩ := p5Actual_gap_solution_pointwise_unique38 n u
  let b : Lib.L2Seq := p6RealInclude38 (p6GapCubeComplete38 n u t)
  have hb : b ∈ p6RealInclude38 '' p5FullRealGapCube38 u :=
    ⟨p6GapCubeComplete38 n u t,p6GapCubeComplete_mem38 n u t ht.1,rfl⟩
  obtain ⟨S,hbase,hSan,hlevel⟩ := hbranch b hb n
  have hbasezero : p2Fn38 n (realSlice u,p2Restrict38 n b)=0 := by
    rw [p6GapCubeComplete_restrict38,← p3RealFn_graph38,ht.2,map_zero]
  refine ⟨t,ht.1,ht.2,S,hbase,hSan,?_⟩
  intro φ hφ
  obtain ⟨hnear,hlev,_huniq⟩ := hlevel φ hφ
  have hz := congrArg (p2Restrict38 n) hlev
  rw [p6PaddedFn_restrict38,p6PaddedFn_restrict38,hbasezero] at hz
  refine ⟨hz,?_⟩
  rw [hbase]
  exact mem_closedBall_iff_norm.mp hnear

end
end NlsGge.GK38
