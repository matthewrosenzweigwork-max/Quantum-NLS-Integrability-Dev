import NlsGge.GK38.AbelianCommonInteriorComplexLevels
import NlsGge.GK38.AbelianFullCompactOperatorLimit

/-! Source-only concrete assembly. The genuine signed operator limit is
supplied by its actual full-gap theorem, including missing row, column and
diagonal. No limit or inverse-norm premise survives in the statement. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6FullGap_common_interior_complex_level_lifts38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R) :
    ∃ r δ B : ℝ, 0 < r ∧ 0 < δ ∧ 0 < B ∧ ball (realSlice u) δ ⊆ gkW ∧
      ∀ b ∈ p6RealInclude38 '' p5FullRealGapCube38 u,
        ∀ φ ∈ ball (realSlice u) δ, ∀ n : ℤ,
          ∃ x : Lib.L2Seq, x ∈ closedBall b (r/2) ∧
            p6PaddedFn38 n (φ,x)=p6PaddedFn38 n (realSlice u,b) ∧
            (∀ y ∈ closedBall b r,
              p6PaddedFn38 n (φ,y)=p6PaddedFn38 n (realSlice u,b) → y=x) ∧
            ∀ y ∈ closedBall b r, (p6PaddedJacobian38 n φ y).IsInvertible ∧
              ‖(p6PaddedJacobian38 n φ y).inverse‖ ≤ B := by
  apply p6FullGap_common_interior_complex_level_lifts_of_signed_limit38 u C R hfam
  intro s hs ε hε
  obtain ⟨N,hN⟩ := p6ActualPadded_Qstar_compact_signed_operator_limit38 u C R hfam ε hε
  refine ⟨N,?_⟩
  intro n hn
  have hcast : (N : ℤ) ≤ (n.natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs] using hn.le
  have hnat : N ≤ n.natAbs := by exact_mod_cast hcast
  exact hN n hnat s hs

end
end NlsGge.GK38
