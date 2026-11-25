import NlsGge.GK38.AbelianJacobianQuotients
import NlsGge.GK38.AbelianPeriodBound

/-! Actual off-diagonal columns and complex row estimates.
UNCOMPILED source preparation; no own-gap factor is ever divided out. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38.P3JacobianColumns
noncomputable section

theorem column_offDiagonal_div_root (n m r : ℤ) (hrn : r ≠ n)
    (s : Lib.L2Seq) (φ : PotPair) (z : ℂ) (hp : (φ,z) ∈ rootDomain38)
    (hsn : Lib.sigmaOf s n-z ≠ 0) (hsr : Lib.sigmaOf s r-z ≠ 0) :
    p3NumeratorColumn38 n r s z/canonRoot38 φ z =
      Complex.I*(Lib.sigmaOf s m-z)*p2OmittedRatio38 m ((φ,s),z)/
        (Lib.sigmaOf s n-z)/(Lib.sigmaOf s r-z)/
        stdRoot38 (tauN φ m) (gamma2 φ m) z := by
  have hroot := canonRoot_ne_zero38 φ hp.1 z hp.2
  have hcol : p3NumeratorColumn38 n r s z/canonRoot38 φ z =
      (p2FullNumerator38 n s z/canonRoot38 φ z)/(Lib.sigmaOf s r-z) := by
    rw [numerator_factor n r hrn s z]
    field_simp [hsr,hroot]
  rw [hcol,p2FullNumerator_div_root38 n m s φ z hp hsn]
  ring

theorem original_disc_reciprocal_bound (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (r m : ℤ) (hrm : r ≠ m)
    (s : Lib.L2Seq) (hσ : Lib.sigmaOf s r ∈ closedBall (C r) (R r))
    (z : ℂ) (hz : z ∈ closedBall (C m) (R m)) :
    ‖1/(Lib.sigmaOf s r-z)‖ ≤ c*Lib.c3w m r := by
  have hd := p2OwnSigma_denominator38 C R c N hg r m hrm s hσ z hz
  have hi : (((r-m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hrm
  have he : 1/(Lib.sigmaOf s r-z) =
      ((((r-m : ℤ) : ℂ))/(Lib.sigmaOf s r-z))/(((r-m : ℤ) : ℂ)) := by
    field_simp [hi,hd.1]
  have hw : ‖(((r-m : ℤ) : ℂ))‖⁻¹ = Lib.c3w m r := by
    rw [Complex.norm_intCast]
    simp only [Int.cast_sub,Lib.c3w,one_div]
  rw [he,norm_div,div_eq_mul_inv,hw]
  exact mul_le_mul_of_nonneg_right hd.2 (Lib.c3w_nonneg m r)

theorem offDiagonal_period_bound (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 φ C R)
    (s : Lib.L2Seq) (n m r : ℤ) (hnm : n ≠ m) (hrn : r ≠ n) (hrm : r ≠ m)
    (hσn : Lib.sigmaOf s n ∈ closedBall (C n) (R n))
    (hσr : Lib.sigmaOf s r ∈ closedBall (C r) (R r)) (H : ℝ) (hH : 0 ≤ H)
    (hbound : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H) :
    ‖(((n-m : ℤ) : ℂ))*abelianPeriod38 m φ (p3NumeratorColumn38 n r s)‖ ≤
      (2*Real.pi*c^2*H)*p2RowEnvelope38 φ s m*Lib.c3w m r := by
  let G : ℂ → ℂ := fun z => Complex.I*
    ((((n-m : ℤ) : ℂ))/(Lib.sigmaOf s n-z))*(Lib.sigmaOf s m-z)*
    p2OmittedRatio38 m ((φ,s),z)*(1/(Lib.sigmaOf s r-z))
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hg.2.2.1
  have hE := p2RowEnvelope_nonneg38 φ s m
  have hw := Lib.c3w_nonneg m r
  have hdn : ∀ z ∈ closedBall (C m) (R m), Lib.sigmaOf s n-z ≠ 0 :=
    fun z hz => (p2OwnSigma_denominator38 C R c N hg n m hnm s hσn z hz).1
  have hdr : ∀ z ∈ closedBall (C m) (R m), Lib.sigmaOf s r-z ≠ 0 :=
    fun z hz => (p2OwnSigma_denominator38 C R c N hg r m hrm s hσr z hz).1
  have hG : AnalyticOnNhd ℂ G (closedBall (C m) (R m)) := by
    exact (((analyticOnNhd_const.mul
      (analyticOnNhd_const.div (analyticOnNhd_const.sub analyticOnNhd_id) hdn)).mul
        (analyticOnNhd_const.sub analyticOnNhd_id)).mul
        (p2OmittedRatio_own_disc_analytic38 m φ hφ C R hfam s)).mul
        (analyticOnNhd_const.div (analyticOnNhd_const.sub analyticOnNhd_id) hdr)
  have hcut : segment ℝ (lamMinus φ m) (lamPlus φ m) ⊆ ball (C m) (R m) := by
    obtain ⟨d,M,hg',hsp⟩ := hfam
    exact (hsp.1 m).1
  have hGB : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖G z‖ ≤ c^2*H*p2RowEnvelope38 φ s m*Lib.c3w m r := by
    intro z hz
    have hzball := ball_subset_closedBall (hcut hz)
    have hn := (p2OwnSigma_denominator38 C R c N hg n m hnm s hσn z hzball).2
    have hr := original_disc_reciprocal_bound C R c N hg r m hrm s hσr z hzball
    have hσm := p2Sigma_cut_envelope38 φ hφ s m z hz
    have he : ‖G z‖ =
        (‖(((n-m : ℤ) : ℂ))/(Lib.sigmaOf s n-z)‖*‖Lib.sigmaOf s m-z‖*
          ‖p2OmittedRatio38 m ((φ,s),z)‖)*‖1/(Lib.sigmaOf s r-z)‖ := by
      simp only [G,norm_mul,Complex.norm_I,one_mul]
    rw [he]
    calc
      _ ≤ ((c*p2RowEnvelope38 φ s m)*H)*(c*Lib.c3w m r) :=
        mul_le_mul
          (mul_le_mul (mul_le_mul hn hσm (norm_nonneg _) hc) (hbound z hz)
            (norm_nonneg _) (mul_nonneg hc hE)) hr
          (norm_nonneg _) (mul_nonneg (mul_nonneg hc hE) hH)
      _ = _ := by ring
  have hr := isolating_radius_pos38 hfam m
  have hτ : tauN φ m = (lamMinus φ m+lamPlus φ m)/2 := by
    rw [tauN_value38 φ hφ m]
    ring
  have hγ := gamma2_value38 φ hφ m
  have hnorm := p2StdRoot_integral_norm_bound38 (lamMinus φ m) (lamPlus φ m)
    (C m) (R m) (c^2*H*p2RowEnvelope38 φ s m*Lib.c3w m r) hr hcut G hG
    (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg c) hH) hE) hw) hGB
  have hfamily := abelianPeriod_fullfamily_realization38 φ hφ (discC φ) C (discR φ) R
    (isolating_family38 φ hφ) hfam m (p3NumeratorColumn38 n r s) (column_entire n r s)
  have heq : EqOn
      (fun z => (((n-m : ℤ) : ℂ))*(p3NumeratorColumn38 n r s z/canonRoot38 φ z))
      (fun z => G z/stdRoot38 ((lamMinus φ m+lamPlus φ m)/2)
        ((lamPlus φ m-lamMinus φ m)^2) z) (sphere (C m) (R m)) := by
    intro z hz
    change (((n-m : ℤ) : ℂ))*(p3NumeratorColumn38 n r s z/canonRoot38 φ z) =
      G z/stdRoot38 ((lamMinus φ m+lamPlus φ m)/2) ((lamPlus φ m-lamMinus φ m)^2) z
    rw [column_offDiagonal_div_root n m r hrn s φ z
      ⟨hφ,fixed_sphere_subset φ C R hfam m hz⟩
      (hdn z (sphere_subset_closedBall hz)) (hdr z (sphere_subset_closedBall hz)),hτ,hγ]
    dsimp [G]
    ring
  have hperiod : (((n-m : ℤ) : ℂ))*abelianPeriod38 m φ (p3NumeratorColumn38 n r s) =
      circleIntegral (fun z => G z/stdRoot38 ((lamMinus φ m+lamPlus φ m)/2)
        ((lamPlus φ m-lamMinus φ m)^2) z) (C m) (R m) := by
    unfold abelianPeriod38
    rw [hfamily.2.2,← circleIntegral.integral_const_mul]
    exact circleIntegral.integral_congr hr.le heq
  rw [hperiod]
  exact hnorm.2.trans_eq (by ring)

end
end NlsGge.GK38.P3JacobianColumns
