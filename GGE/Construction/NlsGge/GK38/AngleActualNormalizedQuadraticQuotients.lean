import NlsGge.GK38.AngleCommonFnZeroSquareMass
import NlsGge.GK38.AngleQuadraticQuotientLp
import NlsGge.GK38.AbelianNormalizedOriginalInputTube
import NlsGge.GK38.AbelianFullCompactOperatorLimit

/-! Concrete actual normalized branches on ONE complex neighborhood before
ALL signed n, with genuine literal root/gamma2 quotients in omitted lp2.
Every ordinary limit, period and placement premise is discharged by actual
model theorems. Upstream science remains source/native-pending; no global
P7 gluing or analyticity of the quotient at collapsed gaps is claimed. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem angleActual_normalized_common_quadratic_quotient_lp38
    (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧ ball (realSlice u) δ ⊆ gkW ∧
      ∀ n : ℤ, ∃ t : P3RealSpace38 n,
        t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0 ∧
        ∃ S : PotPair → Lib.L2Seq,
          S (realSlice u)=p6RealInclude38 (p6GapCubeComplete38 n u t) ∧
          AnalyticOnNhd ℂ S (ball (realSlice u) δ) ∧
          ∀ φ ∈ ball (realSlice u) δ,
            p2Fn38 n (φ,p2Restrict38 n (S φ))=0 ∧
            Lib.sigmaOf (S φ) n=lamMinus (realSlice u) n ∧
            ∃ A : P2Space38 n,
              (∀ m : P2Index38 n,
                A m=(Lib.sigmaOf (S φ) m.1-tauN φ m.1)/gamma2 φ m.1) ∧
              Summable (fun m : P2Index38 n => ‖A m‖^2) ∧
              (∑' m : P2Index38 n,‖A m‖^2) ≤ B ∧
              ∀ m : P2Index38 n,
                Lib.sigmaOf (S φ) m.1=tauN φ m.1+gamma2 φ m.1*A m := by
  have hlimit : ∀ s : P6RealSpace38, s ∈ p5FullRealGapCube38 u →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ n : ℤ, (N : ℤ) < |n| →
          ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)-
            p6Qstar38 (realSlice u) (p6RealInclude38 s)‖ < ε := by
    intro s hs ε hε
    obtain ⟨N,hN⟩ := p6ActualPadded_Qstar_compact_signed_operator_limit38 u C R hfam ε hε
    refine ⟨N,?_⟩
    intro n hn
    have hcast : (N : ℤ) ≤ (n.natAbs : ℤ) := by
      simpa only [Int.natCast_natAbs] using hn.le
    have hnat : N ≤ n.natAbs := by exact_mod_cast hcast
    exact hN n hnat s hs
  obtain ⟨U,V,B,hU,hV,hbase,hUW,hKV,hB,hbound⟩ :=
    angleFullGap_common_Fn_zero_quadratic_square_mass_of_signed_limit38 u C R hfam hlimit
  obtain ⟨ρ,hρ,hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hbase)
  obtain ⟨d,hd,_hdW,hbranches⟩ :=
    p6Normalized_common_complex_original_input_tube38 u C R hfam V hV hKV
  let δ : ℝ := min ρ d
  have hδ : 0 < δ := lt_min hρ hd
  have hsubU : ball (realSlice u) δ ⊆ U :=
    (ball_subset_ball (min_le_left _ _)).trans hρU
  have hsubd : ball (realSlice u) δ ⊆ ball (realSlice u) d :=
    ball_subset_ball (min_le_right _ _)
  refine ⟨δ,B,hδ,hB,hsubU.trans hUW,?_⟩
  intro n
  obtain ⟨t,ht,hzero,S,hSbase,hSan,hSspec⟩ := hbranches n
  refine ⟨t,ht,hzero,S,hSbase,hSan.mono hsubd,?_⟩
  intro φ hφ
  obtain ⟨hsV,hFn,hsn⟩ := hSspec φ (hsubd hφ)
  have hnbase : lamMinus (realSlice u) n ∈ closedBall (C n) (R n) := by
    have hfamily := hfam
    obtain ⟨_c,_N,_hg,hsp⟩ := hfamily
    exact ball_subset_closedBall ((hsp.1 n).1
      (left_mem_segment ℝ (lamMinus (realSlice u) n) (lamPlus (realSlice u) n)))
  have hσ : Lib.sigmaOf (S φ) n ∈ closedBall (C n) (R n) := by rw [hsn]; exact hnbase
  obtain ⟨a,ha0,has,haB,hadev⟩ := (hbound φ (hsubU hφ)).2 (S φ) hsV n hσ hFn
  exact ⟨hFn,hsn,angleActual_quadratic_quotient_lp38 n φ (S φ) a ha0 has B haB hadev⟩

end
end NlsGge.GK38
