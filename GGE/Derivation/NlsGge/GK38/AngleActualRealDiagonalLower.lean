import NlsGge.GK38.AngleDiagonalEquivLower
import NlsGge.GK38.AbelianJacobianDiagonalEquiv
import NlsGge.GK38.AbelianFullRealDiagonalEquiv

/-! Positive ALL-coordinate lower bounds are earned from the ACTUAL real
DIAGONAL equivalences, with their exact coefficient actions. This does not
use the inverse of the full period Jacobian as a diagonal bound. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem angleActual_omitted_real_diagonal_lower38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im=0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k)) (n : ℤ) :
    ∃ d : ℝ, 0 < d ∧ ∀ m : P2Index38 n,
      d ≤ ‖(fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s)))
        (lp.single 2 m (1 : ℝ)) m‖ := by
  have hfamily := hfam
  obtain ⟨c,N,hg,_hsp⟩ := hfamily
  obtain ⟨D,hD⟩ := P3JacobianColumns.actual_real_diagonal_equiv
    u C R c N hg hfam s hs hσ n
  let Q := fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s))
  apply angleReal_diagonal_equiv_lower38 D (fun m => Q (lp.single 2 m (1 : ℝ)) m)
  intro v m
  change D.toContinuousLinearMap v m=Q (lp.single 2 m (1 : ℝ)) m*v m
  rw [hD]
  exact P3DiagonalOperator.actualDiagonal_apply n Q v m

theorem angleActual_full_real_diagonal_lower38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : P6RealSpace38)
    (hσ : ∀ k : ℤ, Lib.sigmaOf (p6RealInclude38 s) k ∈ closedBall (C k) (R k)) :
    ∃ d : ℝ, 0 < d ∧ ∀ m : ℤ,
      d ≤ ‖p6RealQstar38 u s (lp.single 2 m (1 : ℝ)) m‖ := by
  obtain ⟨D,hD⟩ := P6FullJacobian.actual_real_diagonal_equiv u C R hfam s hσ
  apply angleReal_diagonal_equiv_lower38 D
    (fun m => p6RealQstar38 u s (lp.single 2 m (1 : ℝ)) m)
  intro v m
  change D.toContinuousLinearMap v m=p6RealQstar38 u s (lp.single 2 m (1 : ℝ)) m*v m
  rw [hD]
  exact P6DiagonalOperator.actualDiagonal_apply (p6RealQstar38 u s) v m

end
end NlsGge.GK38
