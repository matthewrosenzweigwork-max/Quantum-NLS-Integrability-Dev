import NlsGge.GK38.AbelianNormalizedCommonComplexZeros
import NlsGge.GK38.AbelianGapCubeCompletion
import NlsGge.GK38.AbelianActualPointwiseSolution

/-! Strengthened actual normalized branches retain the padded level identity
to earn EXACT missing-coordinate placement. The nth sigma is the genuine base
lower endpoint on the whole common complex neighborhood, including collapsed
gaps. Older normalized branch contracts are preserved unchanged. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6PaddedFn_self38 (n : ℤ) (φ : PotPair) (s : Lib.L2Seq) :
    p6PaddedFn38 n (φ,s) n=(2 : ℂ)*s n := by
  simp only [p6PaddedFn38,lp.coeFn_add,Pi.add_apply,p2Extend_self38,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.single_apply_self,zero_add]

theorem p6Padded_level_earns_missing_coordinate38 (n : ℤ)
    (φ ψ : PotPair) (s b : Lib.L2Seq)
    (hlevel : p6PaddedFn38 n (φ,s)=p6PaddedFn38 n (ψ,b)) : s n=b n := by
  have h := congrArg (fun x : Lib.L2Seq => x n) hlevel
  rw [p6PaddedFn_self38,p6PaddedFn_self38] at h
  exact (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)) h

theorem p6FullGap_common_complex_normalized_original_placement38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ ball (realSlice u) δ ⊆ gkW ∧
      ∀ n : ℤ, ∃ t : P3RealSpace38 n,
        t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0 ∧
        ∃ S : PotPair → Lib.L2Seq,
          S (realSlice u)=p6RealInclude38 (p6GapCubeComplete38 n u t) ∧
          AnalyticOnNhd ℂ S (ball (realSlice u) δ) ∧
          ∀ φ ∈ ball (realSlice u) δ,
            p2Fn38 n (φ,p2Restrict38 n (S φ))=0 ∧
            ‖S φ-S (realSlice u)‖ ≤ r/2 ∧
            Lib.sigmaOf (S φ) n=lamMinus (realSlice u) n := by
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
  refine ⟨hz,?_,?_⟩
  · rw [hbase]
    exact mem_closedBall_iff_norm.mp hnear
  · have hn : S φ n=b n := p6Padded_level_earns_missing_coordinate38 n φ (realSlice u) (S φ) b hlev
    change countingCenter38 n+S φ n=lamMinus (realSlice u) n
    rw [hn]
    change Lib.sigmaOf (p6RealInclude38 (p6GapCubeComplete38 n u t)) n=_
    rw [p6GapCubeComplete_include38,p5Complete_sigma_self38]

end
end NlsGge.GK38
