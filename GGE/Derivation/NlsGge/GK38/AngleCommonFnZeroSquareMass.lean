import NlsGge.GK38.AngleCommonZeroPeriodSquareMass
import NlsGge.GK38.AngleActualFnZeroPeriods

/-! Actual normalized-Hilbert-zero form of the common quadratic square-mass
bound. The scalar period equations are discharged by the genuine Fn bridge;
no caller supplies a root-deviation or scalar-period oracle. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem angleFullGap_common_Fn_zero_quadratic_square_mass_of_signed_limit38
    (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R)
    (hlimit : ∀ s : P6RealSpace38, s ∈ p5FullRealGapCube38 u →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ n : ℤ, (N : ℤ) < |n| →
          ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)-
            p6Qstar38 (realSlice u) (p6RealInclude38 s)‖ < ε) :
    ∃ U : Set PotPair, ∃ V : Set Lib.L2Seq, ∃ B : ℝ,
      IsOpen U ∧ IsOpen V ∧ realSlice u ∈ U ∧ U ⊆ gkW ∧
      p6RealInclude38 '' p5FullRealGapCube38 u ⊆ V ∧ 0 < B ∧
      ∀ φ ∈ U, IsolatingFamily38 φ C R ∧ ∀ s ∈ V, ∀ n : ℤ,
        Lib.sigmaOf s n ∈ closedBall (C n) (R n) →
        p2Fn38 n (φ,p2Restrict38 n s)=0 →
        ∃ a : ℤ → ℝ, (∀ m, 0 ≤ a m) ∧
          Summable (fun m : ℤ => a m^2) ∧ (∑' m : ℤ, a m^2) ≤ B ∧
          ∀ m : ℤ, n ≠ m →
            ‖Lib.sigmaOf s m-tauN φ m‖ ≤ ‖gamma2 φ m‖*a m := by
  obtain ⟨U,V,B,hU,hV,hbase,hUW,hKV,hB,hbound⟩ :=
    angleFullGap_common_zero_period_quadratic_square_mass_of_signed_limit38
      u C R hfam hlimit
  refine ⟨U,V,B,hU,hV,hbase,hUW,hKV,hB,?_⟩
  intro φ hφ
  refine ⟨(hbound φ hφ).1,?_⟩
  intro s hs n hσ hzero
  exact (hbound φ hφ).2 s hs n hσ
    (angleActual_Fn_zero_implies_periods38 n φ (hUW hφ) s hzero)

end
end NlsGge.GK38
