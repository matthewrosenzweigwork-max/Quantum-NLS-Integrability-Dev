import NlsGge.GK38.AngleRegularFactor
import NlsGge.GK38.AngleActualCommonDiagonalLower
import NlsGge.GK38.AbelianJacobianPeriodError

/-! The literal weighted actual cosine mean is I times the full-padded
Jacobian diagonal. Its common positive bound is EARNED from actual diagonal
operators and a true signed limit, before all varying complex data/labels. -/
set_option autoImplicit false
open Set Metric MeasureTheory
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem angleWeighted_cosine_mean_actual_padded_diagonal38
    (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (n : ℤ) (m : P2Index38 n) (s : Lib.L2Seq)
    (hσ : Lib.sigmaOf s n ∈ closedBall (C n) (R n)) :
    let x : ℝ → ℂ := fun θ => (lamMinus φ m.1+lamPlus φ m.1)/2+
      ((lamPlus φ m.1-lamMinus φ m.1)/2)*(Real.cos θ : ℂ)
    IntervalIntegrable (fun θ : ℝ => (((n-m.1 : ℤ) : ℂ))*
      angleRegularFactor38 n m.1 ((φ,s),x θ)) volume 0 (2*Real.pi) ∧
    (∫ θ : ℝ in (0 : ℝ)..2*Real.pi, (((n-m.1 : ℤ) : ℂ))*
      angleRegularFactor38 n m.1 ((φ,s),x θ)) =
      Complex.I*(p6PaddedJacobian38 n φ s (lp.single 2 m.1 (1 : ℂ)) m.1) := by
  have halg (z : ℂ) : (((n-m.1 : ℤ) : ℂ))*angleRegularFactor38 n m.1 ((φ,s),z)=
      Complex.I*p3DiagonalFactor38 n m.1 φ s z := by
    unfold angleRegularFactor38 p3DiagonalFactor38
    ring
  have havg := P3JacobianColumns.diagonal_period_complex_average φ hφ C R hfam
    s n m.1 m.2.symm hσ
  have hp := p6PaddedJacobian_matrix38 n φ hφ s m m
  constructor
  · simp_rw [halg]
    exact havg.1.const_mul Complex.I
  · simp_rw [halg]
    rw [intervalIntegral.integral_const_mul,← havg.2,← hp]

theorem angleFullGap_common_weighted_cosine_mean_lower_of_signed_limit38
    (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R)
    (hlimit : ∀ s : P6RealSpace38, s ∈ p5FullRealGapCube38 u →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ n : ℤ, (N : ℤ) < |n| →
          ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)-
            p6Qstar38 (realSlice u) (p6RealInclude38 s)‖ < ε) :
    ∃ d : ℝ, ∃ U : Set PotPair, ∃ V : Set Lib.L2Seq,
      0 < d ∧ IsOpen U ∧ IsOpen V ∧ realSlice u ∈ U ∧ U ⊆ gkW ∧
      p6RealInclude38 '' p5FullRealGapCube38 u ⊆ V ∧
      ∀ φ ∈ U, ∀ s ∈ V, ∀ C' : ℤ → ℂ, ∀ R' : ℤ → ℝ,
        IsolatingFamily38 φ C' R' → ∀ n : ℤ, ∀ m : P2Index38 n,
          Lib.sigmaOf s n ∈ closedBall (C' n) (R' n) →
          let x : ℝ → ℂ := fun θ => (lamMinus φ m.1+lamPlus φ m.1)/2+
            ((lamPlus φ m.1-lamMinus φ m.1)/2)*(Real.cos θ : ℂ)
          IntervalIntegrable (fun θ : ℝ => (((n-m.1 : ℤ) : ℂ))*
            angleRegularFactor38 n m.1 ((φ,s),x θ)) volume 0 (2*Real.pi) ∧
          d ≤ ‖∫ θ : ℝ in (0 : ℝ)..2*Real.pi, (((n-m.1 : ℤ) : ℂ))*
            angleRegularFactor38 n m.1 ((φ,s),x θ)‖ := by
  obtain ⟨d,U,V,hd,hU,hV,hbase,hUW,hKV,hbound⟩ :=
    angleFullGap_common_complex_diagonal_lower_of_signed_limit38 u C R hfam hlimit
  refine ⟨d,U,V,hd,hU,hV,hbase,hUW,hKV,?_⟩
  intro φ hφ s hs C' R' hfamily n m hσ
  have hmean := angleWeighted_cosine_mean_actual_padded_diagonal38
    φ (hUW hφ) C' R' hfamily n m s hσ
  refine ⟨hmean.1,?_⟩
  rw [hmean.2,norm_mul,Complex.norm_I,one_mul]
  exact hbound φ hφ s hs n m.1

end
end NlsGge.GK38
