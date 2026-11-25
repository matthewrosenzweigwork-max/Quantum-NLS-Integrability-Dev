import NlsGge.GK38.AbelianNormalizedOriginalInputTube
import NlsGge.GK38.AbelianActualUniformInverseTube
import NlsGge.GK38.AbelianPaddedInverseRestriction

/-! Concrete normalized complex branches carry earned actual inverse bounds
on one common potential neighborhood before ALL signed labels. No signed
limit, branch, continuity or invertibility oracle survives in this statement. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6Normalized_common_complex_inverse_branches38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧ ball (realSlice u) δ ⊆ gkW ∧
      ∀ n : ℤ, ∃ t : P3RealSpace38 n,
        t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0 ∧
        ∃ S : PotPair → Lib.L2Seq,
          S (realSlice u)=p6RealInclude38 (p6GapCubeComplete38 n u t) ∧
          AnalyticOnNhd ℂ S (ball (realSlice u) δ) ∧
          ∀ φ ∈ ball (realSlice u) δ,
            p2Fn38 n (φ,p2Restrict38 n (S φ))=0 ∧
            Lib.sigmaOf (S φ) n=lamMinus (realSlice u) n ∧
            (p6PaddedJacobian38 n φ (S φ)).IsInvertible ∧
            ‖(p6PaddedJacobian38 n φ (S φ)).inverse‖ ≤ B ∧
            (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (φ,y))
              (p2Restrict38 n (S φ))).IsInvertible := by
  obtain ⟨B,U,V,hB,hU,hV,huU,_hUW,hKV,hInv⟩ :=
    p6FullGap_complex_uniform_inverse_bound_tube38 u C R hfam
  obtain ⟨d,hd,hW,hbranches⟩ :=
    p6Normalized_common_complex_original_input_tube38 u C R hfam V hV hKV
  obtain ⟨a,ha,haU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds huU)
  let δ : ℝ := min d a
  have hδ : 0 < δ := lt_min hd ha
  have hdsub : ball (realSlice u) δ ⊆ ball (realSlice u) d :=
    ball_subset_ball (min_le_left _ _)
  have hUsub : ball (realSlice u) δ ⊆ U :=
    (ball_subset_ball (min_le_right _ _)).trans haU
  refine ⟨δ,B,hδ,hB,hdsub.trans hW,?_⟩
  intro n
  obtain ⟨t,ht,htz,S,hbase,han,hspec⟩ := hbranches n
  refine ⟨t,ht,htz,S,hbase,han.mono hdsub,?_⟩
  intro φ hφ
  obtain ⟨hSV,hzero,hmissing⟩ := hspec φ (hdsub hφ)
  obtain ⟨hQ,hQB⟩ := hInv φ (hUsub hφ) (S φ) hSV n
  exact ⟨hzero,hmissing,hQ,hQB,p6PaddedJacobian_earns_omitted_inverse38 n φ (S φ) hQ⟩

end
end NlsGge.GK38
