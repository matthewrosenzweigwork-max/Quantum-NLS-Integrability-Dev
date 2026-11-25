import NlsGge.GK38.AbelianDifferenceDiagonalBound

/-! UNCOMPILED actual off-diagonal difference bound. Both divided factors
belong to OTHER original discs; no own-gap sigma_m factor is divided out. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem p6DifferenceColumn_offDiagonal_period_bound38
    (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (c : ℝ) (N : ℕ) (hg : IsolatingGeometry38 C R c N)
    (hfam : IsolatingFamily38 φ C R) (s : Lib.L2Seq) (n m r : ℤ)
    (hmn : m ≠ n) (hrn : r ≠ n) (hrm : r ≠ m)
    (hσn : Lib.sigmaOf s n ∈ closedBall (C n) (R n))
    (hσr : Lib.sigmaOf s r ∈ closedBall (C r) (R r))
    (H : ℝ) (hH : 0 ≤ H)
    (hRatio : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H) :
    ‖abelianPeriod38 m φ (p6DifferenceColumn38 n m r s)‖ ≤
      (2*c^2*H)*p2RowEnvelope38 φ s m*(‖s n‖+p2RowEnvelope38 φ 0 m)*
        Lib.c3w m n*Lib.c3w m r := by
  let w : ℂ → ℂ := fun z => (z-(m : ℂ)*(Real.pi : ℂ)-s n)/(Real.pi : ℂ)
  let G : ℂ → ℂ := fun z => Complex.I*w z*(Lib.sigmaOf s m-z)*
    p2OmittedRatio38 m ((φ,s),z)*(1/(Lib.sigmaOf s n-z))*(1/(Lib.sigmaOf s r-z))
  let W : ℝ := (‖s n‖+p2RowEnvelope38 φ 0 m)/Real.pi
  let E : ℝ := p2RowEnvelope38 φ s m
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hg.2.2.1
  have hW : 0 ≤ W := div_nonneg
    (add_nonneg (norm_nonneg _) (p2RowEnvelope_nonneg38 φ 0 m)) Real.pi_pos.le
  have hE : 0 ≤ E := p2RowEnvelope_nonneg38 φ s m
  have hwn : 0 ≤ c*Lib.c3w m n := mul_nonneg hc (Lib.c3w_nonneg m n)
  have hwr : 0 ≤ c*Lib.c3w m r := mul_nonneg hc (Lib.c3w_nonneg m r)
  have hdn : ∀ z ∈ closedBall (C m) (R m), Lib.sigmaOf s n-z ≠ 0 :=
    fun z hz => (p2OwnSigma_denominator38 C R c N hg n m hmn.symm s hσn z hz).1
  have hdr : ∀ z ∈ closedBall (C m) (R m), Lib.sigmaOf s r-z ≠ 0 :=
    fun z hz => (p2OwnSigma_denominator38 C R c N hg r m hrm s hσr z hz).1
  have hw : AnalyticOnNhd ℂ w univ := by
    intro z _
    exact ((analyticAt_id.sub analyticAt_const).sub analyticAt_const).div_const
  have hG : AnalyticOnNhd ℂ G (closedBall (C m) (R m)) :=
    (((((analyticOnNhd_const.mul (hw.mono (subset_univ _))).mul
      (analyticOnNhd_const.sub analyticOnNhd_id)).mul
      (p2OmittedRatio_own_disc_analytic38 m φ hφ C R hfam s)).mul
      (analyticOnNhd_const.div (analyticOnNhd_const.sub analyticOnNhd_id) hdn))).mul
      (analyticOnNhd_const.div (analyticOnNhd_const.sub analyticOnNhd_id) hdr)
  have hcut : segment ℝ (lamMinus φ m) (lamPlus φ m) ⊆ ball (C m) (R m) := by
    obtain ⟨_c,_N,_hg,hsp⟩ := hfam
    exact (hsp.1 m).1
  have hGB : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖G z‖ ≤ ((W*E)*H)*(c*Lib.c3w m n)*(c*Lib.c3w m r) := by
    intro z hz
    have hzball := ball_subset_closedBall (hcut hz)
    have hn := P3JacobianColumns.original_disc_reciprocal_bound C R c N hg n m
      hmn.symm s hσn z hzball
    have hr := P3JacobianColumns.original_disc_reciprocal_bound C R c N hg r m
      hrm s hσr z hzball
    have hwz := p6Difference_cut_factor_bound38 φ hφ s n m z hz
    have hσm := p2Sigma_cut_envelope38 φ hφ s m z hz
    have hp1 : ‖w z‖*‖Lib.sigmaOf s m-z‖ ≤ W*E :=
      mul_le_mul hwz hσm (norm_nonneg _) hW
    have hp2 : (‖w z‖*‖Lib.sigmaOf s m-z‖)*‖p2OmittedRatio38 m ((φ,s),z)‖ ≤
        (W*E)*H := mul_le_mul hp1 (hRatio z hz) (norm_nonneg _) (mul_nonneg hW hE)
    have hp3 : ((‖w z‖*‖Lib.sigmaOf s m-z‖)*‖p2OmittedRatio38 m ((φ,s),z)‖)*
        ‖1/(Lib.sigmaOf s n-z)‖ ≤ ((W*E)*H)*(c*Lib.c3w m n) :=
      mul_le_mul hp2 hn (norm_nonneg _) (mul_nonneg (mul_nonneg hW hE) hH)
    simp only [G,norm_mul,Complex.norm_I,one_mul]
    exact mul_le_mul hp3 hr (norm_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg hW hE) hH) hwn)
  have hr := isolating_radius_pos38 hfam m
  have hτ : tauN φ m=(lamMinus φ m+lamPlus φ m)/2 := by
    rw [tauN_value38 φ hφ m]
    ring
  have hγ := gamma2_value38 φ hφ m
  have hB : 0 ≤ ((W*E)*H)*(c*Lib.c3w m n)*(c*Lib.c3w m r) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hW hE) hH) hwn) hwr
  have hnorm := p2StdRoot_integral_norm_bound38 (lamMinus φ m) (lamPlus φ m)
    (C m) (R m) (((W*E)*H)*(c*Lib.c3w m n)*(c*Lib.c3w m r)) hr hcut G hG hB hGB
  have hfamily := abelianPeriod_fullfamily_realization38 φ hφ (discC φ) C
    (discR φ) R (isolating_family38 φ hφ) hfam m
    (p6DifferenceColumn38 n m r s) (p6DifferenceColumn_entire38 n m r s)
  have heq : EqOn
      (fun z => p6DifferenceColumn38 n m r s z/canonRoot38 φ z)
      (fun z => G z/stdRoot38 ((lamMinus φ m+lamPlus φ m)/2)
        ((lamPlus φ m-lamMinus φ m)^2) z) (sphere (C m) (R m)) := by
    intro z hz
    have hzball := sphere_subset_closedBall hz
    have hcol := P3JacobianColumns.column_offDiagonal_div_root n m r hrn s φ z
      ⟨hφ,fixed_sphere_subset φ C R hfam m hz⟩ (hdn z hzball) (hdr z hzball)
    rw [hτ,hγ] at hcol
    change w z*p3NumeratorColumn38 n r s z/canonRoot38 φ z = _
    rw [mul_div_assoc,hcol]
    dsimp [G]
    ring
  have hperiod : abelianPeriod38 m φ (p6DifferenceColumn38 n m r s)=
      circleIntegral (fun z => G z/stdRoot38 ((lamMinus φ m+lamPlus φ m)/2)
        ((lamPlus φ m-lamMinus φ m)^2) z) (C m) (R m) := by
    unfold abelianPeriod38
    rw [hfamily.2.2]
    exact circleIntegral.integral_congr hr.le heq
  rw [hperiod]
  exact hnorm.2.trans_eq (by dsimp [W,E]; field_simp [Real.pi_ne_zero])

theorem p6ActualDifference_offDiagonal_bound38
    (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (c : ℝ) (N : ℕ) (hg : IsolatingGeometry38 C R c N)
    (hfam : IsolatingFamily38 φ C R) (s : Lib.L2Seq)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (H : ℝ) (hH : 0 ≤ H)
    (hRatio : ∀ m : ℤ, ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H)
    (n m r : ℤ) (hmn : m ≠ n) (hrn : r ≠ n) (hrm : r ≠ m) :
    ‖(p6PaddedJacobian38 n φ s-p6Qstar38 φ s) (lp.single 2 r (1 : ℂ)) m‖ ≤
      (2*c^2*H)*p2RowEnvelope38 φ s m*(‖s n‖+p2RowEnvelope38 φ 0 m)*
        Lib.c3w m n*Lib.c3w m r := by
  rw [p6Padded_minus_Qstar_matrix_period38 n φ hφ s ⟨m,hmn⟩ ⟨r,hrn⟩]
  exact p6DifferenceColumn_offDiagonal_period_bound38 φ hφ C R c N hg hfam s n m r
    hmn hrn hrm (hσ n) (hσ r) H hH (hRatio m)

end
end NlsGge.GK38
