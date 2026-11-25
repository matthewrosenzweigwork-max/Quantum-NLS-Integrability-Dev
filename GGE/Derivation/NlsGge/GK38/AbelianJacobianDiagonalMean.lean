import NlsGge.GK38.AbelianJacobianQuotients
import NlsGge.GK38.AbelianRealMeanValue

/-! Actual real diagonal mean on the original isolating discs, including collapsed gaps.
UNCOMPILED source preparation. The normalization is +2π, hence the free diagonal is 2. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.P3JacobianColumns
noncomputable section

theorem diagonal_period_mean (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im = 0)
    (n m : ℤ) (hmn : m ≠ n)
    (hσ : Lib.sigmaOf s n ∈ closedBall (C n) (R n)) :
    ∃ x ∈ Icc (actualGapLowerAllE02_38 u m) (actualGapUpperAllE02_38 u m),
      (((n-m : ℤ) : ℂ)) *
        abelianPeriod38 m (realSlice u) (p3NumeratorColumn38 n m s) =
      (2*(Real.pi : ℂ))*p3DiagonalFactor38 n m (realSlice u) s (x : ℂ) := by
  let φ : PotPair := realSlice u
  let a : ℝ := actualGapLowerAllE02_38 u m
  let b : ℝ := actualGapUpperAllE02_38 u m
  let G : ℂ → ℂ := p3DiagonalFactor38 n m φ s
  let S : ℂ → ℂ := stdRoot38 (((a : ℂ)+b)/2) (((b : ℂ)-a)^2)
  have hφ : φ ∈ gkW := realSlice_mem_gkW u
  have hr : 0 < R m := isolating_radius_pos38 hfam m
  have hab : a ≤ b := (gap_endpoint_levels38 u m).1
  have hends := lamPlus_real u m
  have hcut : segment ℝ (a : ℂ) (b : ℂ) ⊆ ball (C m) (R m) := by
    obtain ⟨c,N,hg,hsp⟩ := hfam
    simpa only [hends.1,hends.2] using (hsp.1 m).1
  have hseg : ∀ x ∈ Icc a b, (x : ℂ) ∈ segment ℝ (a : ℂ) (b : ℂ) := by
    intro x hx
    have hi : x ∈ segment ℝ a b := by simpa only [segment_eq_Icc hab] using hx
    have himg := image_segment ℝ (Complex.ofRealCLM.toLinearMap.toAffineMap) a b
    change (Complex.ofRealCLM.toLinearMap.toAffineMap x) ∈
      segment ℝ (Complex.ofRealCLM.toLinearMap.toAffineMap a)
        (Complex.ofRealCLM.toLinearMap.toAffineMap b)
    rw [← himg]
    exact ⟨x,hi,rfl⟩
  have hG : AnalyticOnNhd ℂ G (closedBall (C m) (R m)) :=
    diagonalFactor_analytic φ hφ C R hfam n m hmn.symm s hσ
  have hGr : ∀ x ∈ Icc a b, (G (x : ℂ)).im = 0 := by
    intro x hx
    exact diagonalFactor_real u s hs n m x
      (a5OwnClosedBall_omittedDomain38 φ hφ C R hfam m x
        (ball_subset_closedBall (hcut (hseg x hx))))
  have hd : ∀ z ∈ closedBall (C m) (R m), Lib.sigmaOf s n-z ≠ 0 := by
    obtain ⟨c,N,hgeom,_hsp⟩ := hfam
    intro z hz
    exact (p2OwnSigma_denominator38 C R c N hgeom n m hmn.symm s hσ z hz).1
  have hτ : tauN φ m = ((a : ℂ)+b)/2 := by
    rw [tauN_value38 φ hφ m]
    change (lamPlus (realSlice u) m+lamMinus (realSlice u) m)/2 = _
    rw [hends.1,hends.2]
    ring
  have hγ : gamma2 φ m = ((b : ℂ)-a)^2 := by
    rw [gamma2_value38 φ hφ m]
    change (lamPlus (realSlice u) m-lamMinus (realSlice u) m)^2 = _
    rw [hends.1,hends.2]
  have hfamily := abelianPeriod_fullfamily_realization38 φ hφ (discC φ) C (discR φ) R
    (isolating_family38 φ hφ) hfam m (p3NumeratorColumn38 n m s)
    (column_entire n m s)
  have heq : EqOn
      (fun z => (((n-m : ℤ) : ℂ))*(p3NumeratorColumn38 n m s z/canonRoot38 φ z))
      (fun z => Complex.I*(G z/S z)) (sphere (C m) (R m)) := by
    intro z hz
    have he := weighted_column_diagonal_integrand n m hmn s φ z
      ⟨hφ,fixed_sphere_subset φ C R hfam m hz⟩ (hd z (sphere_subset_closedBall hz))
    simpa only [hτ,hγ,mul_div_assoc] using he
  have hperiod : (((n-m : ℤ) : ℂ))*abelianPeriod38 m φ (p3NumeratorColumn38 n m s) =
      Complex.I*circleIntegral (fun z => G z/S z) (C m) (R m) := by
    unfold abelianPeriod38
    rw [hfamily.2.2,← circleIntegral.integral_const_mul,
      circleIntegral.integral_congr hr.le heq,circleIntegral.integral_const_mul]
  obtain ⟨x,hx,hmean⟩ := p2StdRoot_real_mean_value38 a b hab (C m) (R m)
    hr hcut G hG hGr
  change (1/(2*(Real.pi : ℂ)*Complex.I))*
    circleIntegral (fun z => G z/S z) (C m) (R m) = -G (x : ℂ) at hmean
  have h2 : 2*(Real.pi : ℂ)*Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hscaled := congrArg (fun w : ℂ => (2*(Real.pi : ℂ)*Complex.I)*w) hmean
  rw [← mul_assoc,mul_one_div_cancel h2,one_mul] at hscaled
  refine ⟨x,hx,?_⟩
  rw [hperiod,hscaled]
  calc
    _ = -(2*(Real.pi : ℂ)*G (x : ℂ))*(Complex.I*Complex.I) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem diagonal_period_ne_zero (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im = 0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (n m : ℤ) (hmn : m ≠ n) :
    (((n-m : ℤ) : ℂ))*abelianPeriod38 m (realSlice u) (p3NumeratorColumn38 n m s) ≠ 0 := by
  obtain ⟨x,hx,hmean⟩ := diagonal_period_mean u C R hfam s hs n m hmn (hσ n)
  have hab := (gap_endpoint_levels38 u m).1
  have hi : x ∈ segment ℝ (actualGapLowerAllE02_38 u m)
      (actualGapUpperAllE02_38 u m) := by
    simpa only [segment_eq_Icc hab] using hx
  have himg := image_segment ℝ (Complex.ofRealCLM.toLinearMap.toAffineMap)
    (actualGapLowerAllE02_38 u m) (actualGapUpperAllE02_38 u m)
  have hxc : (x : ℂ) ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m) := by
    rw [(lamPlus_real u m).1,(lamPlus_real u m).2]
    change (Complex.ofRealCLM.toLinearMap.toAffineMap x) ∈
      segment ℝ (Complex.ofRealCLM.toLinearMap.toAffineMap (actualGapLowerAllE02_38 u m))
        (Complex.ofRealCLM.toLinearMap.toAffineMap (actualGapUpperAllE02_38 u m))
    rw [← himg]
    exact ⟨x,hi,rfl⟩
  have hxball : (x : ℂ) ∈ closedBall (C m) (R m) := by
    obtain ⟨c,N,hg,hsp⟩ := hfam
    exact ball_subset_closedBall ((hsp.1 m).1 hxc)
  rw [hmean]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
    (diagonalFactor_ne_zero (realSlice u) (realSlice_mem_gkW u) C R hfam
      s hσ n m hmn.symm x hxball)

end
end NlsGge.GK38.P3JacobianColumns
