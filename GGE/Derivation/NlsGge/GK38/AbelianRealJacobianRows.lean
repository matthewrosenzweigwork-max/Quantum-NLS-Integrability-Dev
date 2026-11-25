import NlsGge.GK38.AbelianJacobianOffDiagonalRows
import NlsGge.GK38.AbelianJacobianPeriods
import NlsGge.GK38.AbelianRealJacobian
import NlsGge.GK38.AbelianRealDiagonalOperator

/-! Actual real Q and actual off-diagonal K inherit the source row bound.
UNCOMPILED source preparation. HS summability/Parseval is not asserted here. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38.P3JacobianColumns
noncomputable section

theorem actual_real_matrix_coordinate (u : PhysicalL2) (s : Lib.L2Seq)
    (hs : ∀ k : ℤ, (s k).im = 0) (n : ℤ) (m r : P2Index38 n) :
    (((fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s)))
      (lp.single 2 r (1 : ℝ)) m : ℝ) : ℂ) =
      (((n-m.1 : ℤ) : ℂ))*abelianPeriod38 m.1 (realSlice u)
        (p3NumeratorColumn38 n r.1 s) := by
  let t : P3RealSpace38 n := p3RealPart38 n (p2Restrict38 n s)
  have hre : p2RealSeq38 n (p2Restrict38 n s) := by
    intro k
    simpa only [p2Restrict_apply38] using hs k.1
  have hinc : p3RealInclude38 n t = p2Restrict38 n s :=
    p3RealInclude_realPart38 n (p2Restrict38 n s) hre
  have hb := p3RealFn_fderiv_include38 n u t
  have he := congrArg
    (fun T : P3RealSpace38 n →L[ℝ] P2Space38 n => T (lp.single 2 r (1 : ℝ)) m) hb
  have hJ : p3RealIncludeCLM38 n (lp.single 2 r (1 : ℝ)) =
      lp.single 2 r (1 : ℂ) := p3RealInclude_single38 n r
  simp only [ContinuousLinearMap.comp_apply,hJ] at he
  change (((fderiv ℝ (p3RealFn38 n u) t) (lp.single 2 r (1 : ℝ)) m : ℝ) : ℂ) =
    (fderiv ℂ (fun v : P2Space38 n => p2Fn38 n (realSlice u,v))
      (p3RealInclude38 n t)) (lp.single 2 r (1 : ℂ)) m at he
  rw [hinc,matrix_coordinate n m r (realSlice u) (realSlice_mem_gkW u)] at he
  have hcol : p3NumeratorColumn38 n r.1 (p2Extend38 n (p2Restrict38 n s)) =
      p3NumeratorColumn38 n r.1 s := funext (column_extend_restrict n r.1 s)
  rw [hcol] at he
  exact he

theorem actual_real_offDiagonal_coefficient_bound (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im = 0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (H : ℝ) (hH : 0 ≤ H)
    (hbound : ∀ m : ℤ, ∀ z ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m),
      ‖p2OmittedRatio38 m (((realSlice u),s),z)‖ ≤ H)
    (n : ℤ) (m r : P2Index38 n) (hrm : r ≠ m) :
    ‖(fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s)))
      (lp.single 2 r (1 : ℝ)) m‖ ≤
      (2*Real.pi*c^2*H)*p2RowEnvelope38 (realSlice u) s m.1*Lib.c3w m.1 r.1 := by
  have hrm' : r.1 ≠ m.1 := fun h => hrm (Subtype.ext h)
  have he := actual_real_matrix_coordinate u s hs n m r
  calc
    _ = ‖(((fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s)))
        (lp.single 2 r (1 : ℝ)) m : ℝ) : ℂ)‖ := (Complex.norm_real _).symm
    _ = ‖(((n-m.1 : ℤ) : ℂ))*abelianPeriod38 m.1 (realSlice u)
        (p3NumeratorColumn38 n r.1 s)‖ := congrArg norm he
    _ ≤ _ := offDiagonal_period_bound (realSlice u) (realSlice_mem_gkW u)
      C R c N hg hfam s n m.1 r.1 m.2.symm r.2 hrm' (hσ n) (hσ r.1)
      H hH (hbound m.1)

theorem actual_real_K_row_bound (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im = 0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (H : ℝ) (hH : 0 ≤ H)
    (hbound : ∀ m : ℤ, ∀ z ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m),
      ‖p2OmittedRatio38 m (((realSlice u),s),z)‖ ≤ H)
    (n : ℤ) (m r : P2Index38 n) :
    ‖P3DiagonalOperator.actualOffDiagonal n
      (fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s)))
        (lp.single 2 r (1 : ℝ)) m‖ ≤
      (2*Real.pi*c^2*H)*p2RowEnvelope38 (realSlice u) s m.1*Lib.c3w m.1 r.1 := by
  let Q := fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s))
  by_cases hrm : r = m
  · subst r
    rw [P3DiagonalOperator.actualOffDiagonal_diagonal_zero,norm_zero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg c)) hH)
        (p2RowEnvelope_nonneg38 (realSlice u) s m.1)) (Lib.c3w_nonneg m.1 m.1)
  · have hD : P3DiagonalOperator.actualDiagonal n Q (lp.single 2 r (1 : ℝ)) m = 0 := by
      rw [P3DiagonalOperator.actualDiagonal_apply,
        lp.single_apply_ne (E := fun _ : P2Index38 n => ℝ) 2 r (1 : ℝ) (Ne.symm hrm),mul_zero]
    change ‖Q (lp.single 2 r (1 : ℝ)) m-
      P3DiagonalOperator.actualDiagonal n Q (lp.single 2 r (1 : ℝ)) m‖ ≤ _
    rw [hD,sub_zero]
    exact actual_real_offDiagonal_coefficient_bound u C R c N hg hfam s hs hσ H hH hbound n m r hrm

end
end NlsGge.GK38.P3JacobianColumns
