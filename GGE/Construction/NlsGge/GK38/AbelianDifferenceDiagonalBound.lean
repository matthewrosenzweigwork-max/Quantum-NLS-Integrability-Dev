import NlsGge.GK38.AbelianDifferenceCutEnvelope
import NlsGge.GK38.AbelianJacobianOffDiagonalRows

/-! UNCOMPILED actual nonmissing diagonal difference bound. The entire
polynomial difference factor and the actual omitted ratio are analytic on
the original filled disc; only the OTHER input sigma_n is divided out. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem p6DifferenceColumn_diagonal_period_bound38
    (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (c : ℝ) (N : ℕ) (hg : IsolatingGeometry38 C R c N)
    (hfam : IsolatingFamily38 φ C R) (s : Lib.L2Seq) (n m : ℤ) (hmn : m ≠ n)
    (hσn : Lib.sigmaOf s n ∈ closedBall (C n) (R n))
    (H : ℝ) (hH : 0 ≤ H)
    (hRatio : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H) :
    ‖abelianPeriod38 m φ (p6DifferenceColumn38 n m m s)‖ ≤
      (2*c*H)*(‖s n‖+p2RowEnvelope38 φ 0 m)*Lib.c3w m n := by
  let w : ℂ → ℂ := fun z => (z-(m : ℂ)*(Real.pi : ℂ)-s n)/(Real.pi : ℂ)
  let G : ℂ → ℂ := fun z => Complex.I*w z*p2OmittedRatio38 m ((φ,s),z)*
    (1/(Lib.sigmaOf s n-z))
  let W : ℝ := (‖s n‖+p2RowEnvelope38 φ 0 m)/Real.pi
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hg.2.2.1
  have hW : 0 ≤ W := div_nonneg
    (add_nonneg (norm_nonneg _) (p2RowEnvelope_nonneg38 φ 0 m)) Real.pi_pos.le
  have hdn : ∀ z ∈ closedBall (C m) (R m), Lib.sigmaOf s n-z ≠ 0 :=
    fun z hz => (p2OwnSigma_denominator38 C R c N hg n m hmn.symm s hσn z hz).1
  have hw : AnalyticOnNhd ℂ w univ := by
    intro z _
    exact ((analyticAt_id.sub analyticAt_const).sub analyticAt_const).div_const
  have hG : AnalyticOnNhd ℂ G (closedBall (C m) (R m)) :=
    ((analyticOnNhd_const.mul (hw.mono (subset_univ _))).mul
      (p2OmittedRatio_own_disc_analytic38 m φ hφ C R hfam s)).mul
      (analyticOnNhd_const.div (analyticOnNhd_const.sub analyticOnNhd_id) hdn)
  have hcut : segment ℝ (lamMinus φ m) (lamPlus φ m) ⊆ ball (C m) (R m) := by
    obtain ⟨_c,_N,_hg,hsp⟩ := hfam
    exact (hsp.1 m).1
  have hGB : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖G z‖ ≤ W*H*(c*Lib.c3w m n) := by
    intro z hz
    have hn := P3JacobianColumns.original_disc_reciprocal_bound C R c N hg n m
      hmn.symm s hσn z (ball_subset_closedBall (hcut hz))
    have hwz := p6Difference_cut_factor_bound38 φ hφ s n m z hz
    have he : ‖G z‖ = ‖w z‖*‖p2OmittedRatio38 m ((φ,s),z)‖*
        ‖1/(Lib.sigmaOf s n-z)‖ := by simp only [G,norm_mul,Complex.norm_I,one_mul]
    rw [he]
    exact mul_le_mul
      (mul_le_mul hwz (hRatio z hz) (norm_nonneg _) hW)
      hn (norm_nonneg _) (mul_nonneg hW hH)
  have hr := isolating_radius_pos38 hfam m
  have hτ : tauN φ m=(lamMinus φ m+lamPlus φ m)/2 := by
    rw [tauN_value38 φ hφ m]
    ring
  have hγ := gamma2_value38 φ hφ m
  have hB : 0 ≤ W*H*(c*Lib.c3w m n) :=
    mul_nonneg (mul_nonneg hW hH) (mul_nonneg hc (Lib.c3w_nonneg m n))
  have hnorm := p2StdRoot_integral_norm_bound38 (lamMinus φ m) (lamPlus φ m)
    (C m) (R m) (W*H*(c*Lib.c3w m n)) hr hcut G hG hB hGB
  have hfamily := abelianPeriod_fullfamily_realization38 φ hφ (discC φ) C
    (discR φ) R (isolating_family38 φ hφ) hfam m
    (p6DifferenceColumn38 n m m s) (p6DifferenceColumn_entire38 n m m s)
  have heq : EqOn
      (fun z => p6DifferenceColumn38 n m m s z/canonRoot38 φ z)
      (fun z => G z/stdRoot38 ((lamMinus φ m+lamPlus φ m)/2)
        ((lamPlus φ m-lamMinus φ m)^2) z) (sphere (C m) (R m)) := by
    intro z hz
    have hcol := P3JacobianColumns.column_diagonal_div_root n m hmn s φ z
      ⟨hφ,fixed_sphere_subset φ C R hfam m hz⟩ (hdn z (sphere_subset_closedBall hz))
    rw [hτ,hγ] at hcol
    change w z*p3NumeratorColumn38 n m s z/canonRoot38 φ z = _
    rw [mul_div_assoc,hcol]
    dsimp [G]
    ring
  have hperiod : abelianPeriod38 m φ (p6DifferenceColumn38 n m m s)=
      circleIntegral (fun z => G z/stdRoot38 ((lamMinus φ m+lamPlus φ m)/2)
        ((lamPlus φ m-lamMinus φ m)^2) z) (C m) (R m) := by
    unfold abelianPeriod38
    rw [hfamily.2.2]
    exact circleIntegral.integral_congr hr.le heq
  rw [hperiod]
  exact hnorm.2.trans_eq (by dsimp [W]; field_simp [Real.pi_ne_zero])

theorem p6ActualDifference_diagonal_bound38
    (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (c : ℝ) (N : ℕ) (hg : IsolatingGeometry38 C R c N)
    (hfam : IsolatingFamily38 φ C R) (s : Lib.L2Seq)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (H : ℝ) (hH : 0 ≤ H)
    (hRatio : ∀ m : ℤ, ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H) (n m : ℤ) (hmn : m ≠ n) :
    ‖(p6PaddedJacobian38 n φ s-p6Qstar38 φ s) (lp.single 2 m (1 : ℂ)) m‖ ≤
      (2*c*H)*(‖s n‖+p2RowEnvelope38 φ 0 m)*Lib.c3w m n := by
  rw [p6Padded_minus_Qstar_matrix_period38 n φ hφ s ⟨m,hmn⟩ ⟨m,hmn⟩]
  exact p6DifferenceColumn_diagonal_period_bound38 φ hφ C R c N hg hfam s n m hmn
    (hσ n) H hH (hRatio m)

end
end NlsGge.GK38
