import NlsGge.GK38.AbelianJacobianUniformRows

/-! Actual original-family real Jacobian decomposition with one local uniform
column-energy bound for every signed omitted index. Draft pending review/native. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot
namespace NlsGge.GK38.P3JacobianColumns
noncomputable section
open NlsGge.Analysis.RegularizedDeterminant

theorem original_family_uniform_real_jacobian (u₀ : PhysicalL2)
    (s₀ : Lib.L2Seq) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam₀ : IsolatingFamily38 (realSlice u₀) C R)
    (hσ₀ : ∀ k : ℤ, Lib.sigmaOf s₀ k ∈ ball (C k) (R k)) :
    ∃ U : Set PotPair, U ∈ 𝓝 (realSlice u₀) ∧ U ⊆ gkW ∧
    ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ u : PhysicalL2, realSlice u ∈ U → ∀ s ∈ V,
        (∀ k : ℤ, (s k).im = 0) → ∀ n : ℤ,
        ∃ (D : P3RealSpace38 n ≃L[ℝ] P3RealSpace38 n)
          (K : P3RealSpace38 n →L[ℝ] P3RealSpace38 n),
          let Q := fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s))
          Q = D.toContinuousLinearMap+K ∧
          D.toContinuousLinearMap = P3DiagonalOperator.actualDiagonal n Q ∧
          K = P3DiagonalOperator.actualOffDiagonal n Q ∧
          IsHilbertSchmidt K ∧ IsCompactOperator K ∧
          (∀ m : P2Index38 n, K (lp.single 2 m (1 : ℝ)) m = 0) ∧
          Summable (fun r : P2Index38 n => ‖K (lp.single 2 r (1 : ℝ))‖^2) ∧
          (∑' r : P2Index38 n, ‖K (lp.single 2 r (1 : ℝ))‖^2) ≤ B := by
  obtain ⟨U,hU,hUW,V,hV,c,N,B,hg,hfamily,hσ,hB,hrows⟩ :=
    original_family_uniform_complex_rows (realSlice u₀) (realSlice_mem_gkW u₀)
      s₀ C R hfam₀ hσ₀
  refine ⟨U,hU,hUW,V,hV,Lib.invSqSum*B,mul_nonneg Lib.invSqSum_nonneg hB,?_⟩
  intro u hu s hs hsreal n
  let Q := fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s))
  let K := P3DiagonalOperator.actualOffDiagonal n Q
  have hfam := hfamily (realSlice u) hu
  have hσclosed (k : ℤ) : Lib.sigmaOf s k ∈ closedBall (C k) (R k) :=
    ball_subset_closedBall (hσ s hs k)
  obtain ⟨a,e,_ha0,he0,_has,hes,_haB,heB,_hdiag,hoff⟩ := hrows (realSlice u) hu s hs
  have hKrow (m r : P2Index38 n) :
      ‖K (lp.single 2 r (1 : ℝ)) m‖ ≤ e m.1*Lib.c3w m.1 r.1 := by
    by_cases hrm : r = m
    · subst r
      rw [P3DiagonalOperator.actualOffDiagonal_diagonal_zero,norm_zero]
      exact mul_nonneg (he0 m.1) (Lib.c3w_nonneg m.1 m.1)
    · have hD : P3DiagonalOperator.actualDiagonal n Q (lp.single 2 r (1 : ℝ)) m = 0 := by
        rw [P3DiagonalOperator.actualDiagonal_apply,
          lp.single_apply_ne (E := fun _ : P2Index38 n => ℝ) 2 r (1 : ℝ) (Ne.symm hrm),mul_zero]
      change ‖Q (lp.single 2 r (1 : ℝ)) m-
        P3DiagonalOperator.actualDiagonal n Q (lp.single 2 r (1 : ℝ)) m‖ ≤ _
      rw [hD,sub_zero]
      have hq := hoff n m r hrm
      rw [matrix_coordinate n m r (realSlice u) (realSlice_mem_gkW u)] at hq
      have hcol : p3NumeratorColumn38 n r.1 (p2Extend38 n (p2Restrict38 n s)) =
          p3NumeratorColumn38 n r.1 s := funext (column_extend_restrict n r.1 s)
      rw [hcol] at hq
      calc
        _ = ‖((Q (lp.single 2 r (1 : ℝ)) m : ℝ) : ℂ)‖ := (Complex.norm_real _).symm
        _ = ‖(((n-m.1 : ℤ) : ℂ))*abelianPeriod38 m.1 (realSlice u)
            (p3NumeratorColumn38 n r.1 s)‖ :=
          congrArg norm (actual_real_matrix_coordinate u s hsreal n m r)
        _ ≤ _ := hq
  obtain ⟨hHS,hSum,hMass⟩ := P3OperatorBridge.matrix_row_bound_isHS n K e 1
    (by norm_num) he0 hes (by simpa only [one_mul] using hKrow)
  have hUniform : (∑' r : P2Index38 n, ‖K (lp.single 2 r (1 : ℝ))‖^2) ≤
      Lib.invSqSum*B := by
    apply hMass.trans
    simpa only [one_pow,one_mul] using
      mul_le_mul_of_nonneg_left heB Lib.invSqSum_nonneg
  obtain ⟨D,hD⟩ := actual_real_diagonal_equiv u C R c N hg hfam s hsreal hσclosed n
  refine ⟨D,K,?_,hD,rfl,hHS,P3OperatorBridge.hilbertSchmidt_isCompact K hHS,
    P3DiagonalOperator.actualOffDiagonal_diagonal_zero n Q,hSum,hUniform⟩
  rw [hD]
  exact P3DiagonalOperator.actual_decomposition n Q

end
end NlsGge.GK38.P3JacobianColumns
