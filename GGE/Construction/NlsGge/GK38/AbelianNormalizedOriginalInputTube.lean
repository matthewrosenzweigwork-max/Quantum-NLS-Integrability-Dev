import NlsGge.GK38.AbelianNormalizedOriginalPlacement
import NlsGge.GK38.AbelianCommonHolomorphicRange

/-! Actual normalized analytic zeros stay in ANY prescribed open input tube
around the compact full real gap cube, on one potential neighborhood before
ALL signed labels. The uniform radius follows from the actual Cauchy bound. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6Normalized_common_complex_original_input_tube38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (V : Set Lib.L2Seq) (hV : IsOpen V)
    (hKV : p6RealInclude38 '' p5FullRealGapCube38 u ⊆ V) :
    ∃ δ : ℝ, 0 < δ ∧ ball (realSlice u) δ ⊆ gkW ∧
      ∀ n : ℤ, ∃ t : P3RealSpace38 n,
        t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0 ∧
        ∃ S : PotPair → Lib.L2Seq,
          S (realSlice u)=p6RealInclude38 (p6GapCubeComplete38 n u t) ∧
          AnalyticOnNhd ℂ S (ball (realSlice u) δ) ∧
          ∀ φ ∈ ball (realSlice u) δ,
            S φ ∈ V ∧ p2Fn38 n (φ,p2Restrict38 n (S φ))=0 ∧
            Lib.sigmaOf (S φ) n=lamMinus (realSlice u) n := by
  classical
  obtain ⟨r,d,hr,hd,hW,hbranches⟩ :=
    p6FullGap_common_complex_normalized_original_placement38 u C R hfam
  choose t ht hzero S hbase han hspec using hbranches
  let K : Set Lib.L2Seq := p6RealInclude38 '' p5FullRealGapCube38 u
  have hK : IsCompact K :=
    (p5FullRealGapCube_isCompact38 u).image p6RealInclude38.continuous
  have hb (n : ℤ) : S n (realSlice u) ∈ K := by
    rw [hbase n]
    exact ⟨p6GapCubeComplete38 n u (t n),p6GapCubeComplete_mem38 n u (t n) (ht n),rfl⟩
  obtain ⟨δ,hδ,hδd,hrange⟩ :=
    P6HolomorphicBounds.common_range_of_uniform_holomorphic_bound K V hK hV hKV
      S (fun n => S n (realSlice u)) (realSlice u) d (r/2) hd (half_pos hr).le hb
      (fun _ => rfl) han (fun n φ hφ => (hspec n φ hφ).2.1)
  have hsub : ball (realSlice u) δ ⊆ ball (realSlice u) d :=
    ball_subset_ball (hδd.trans (by linarith))
  refine ⟨δ,hδ,hsub.trans hW,?_⟩
  intro n
  refine ⟨t n,ht n,hzero n,S n,hbase n,(han n).mono hsub,?_⟩
  intro φ hφ
  exact ⟨(hrange n φ hφ).1,(hspec n φ (hsub hφ)).1,(hspec n φ (hsub hφ)).2.2⟩

end
end NlsGge.GK38
