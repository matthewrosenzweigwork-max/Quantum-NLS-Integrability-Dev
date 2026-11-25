import NlsGge.GK38.AbelianPaddedOperatorInverse
import NlsGge.GK38.AbelianPaddedJacobianColumns
import NlsGge.GK38.AbelianFullCompactInverseBound
import NlsGge.GK38.AbelianComplexJacobianInverse

/-! Actual padded Qn invertibility on every ORIGINAL closed real placement.
No Fn-zero premise, missing-coordinate zero extension, or inverse oracle. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6PaddedJacobian_original_real_inverse38 (n : ℤ) (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s : Lib.L2Seq)
    (hs : ∀ k : ℤ, (s k).im=0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k)) :
    (p6PaddedJacobian38 n (realSlice u) s).IsInvertible := by
  have hreal : (fderiv ℝ (p3RealFn38 n u)
      (p3RealPart38 n (p2Restrict38 n s))).IsInvertible :=
    P4NumeratorVariation.original_family_real_jacobian_inverse n u C R hfam s hs hσ
  have hc := P4NumeratorVariation.complex_jacobian_inverse_of_real_inverse n u
    (p3RealPart38 n (p2Restrict38 n s)) hreal
  have hJ : p3RealInclude38 n (p3RealPart38 n (p2Restrict38 n s))=p2Restrict38 n s :=
    p3RealInclude_realPart38 n _ (fun m => hs m.val)
  rw [hJ] at hc
  change (p6PadOperator38 n
    (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t)) (p2Restrict38 n s))).IsInvertible
  exact p6PadOperator_isInvertible38 n _ hc

theorem p6PaddedJacobian_full_gap_inverse38 (n : ℤ) (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s : P6RealSpace38)
    (hs : s ∈ p5FullRealGapCube38 u) :
    (p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)).IsInvertible :=
  p6PaddedJacobian_original_real_inverse38 n u C R hfam (p6RealInclude38 s)
    (fun k => Complex.ofReal_im (s k))
    (P6FullJacobian.full_gap_original_family_placement u C R hfam s hs)

end
end NlsGge.GK38
