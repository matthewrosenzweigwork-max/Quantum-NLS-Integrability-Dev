import NlsGge.GK38.AbelianFullColumnPeriods
import NlsGge.GK38.AbelianJacobianGeometry
import NlsGge.GK38.AbelianRealMeanValue

/-! Actual full-Jacobian diagonal: the own numerator factor has already been
removed, so there is no division by sigma_m-z, even at a collision. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.P6FullJacobian
noncomputable section

theorem fullColumn_diagonal_div_root (m : ℤ) (s : Lib.L2Seq)
    (φ : PotPair) (z : ℂ) (hp : (φ,z) ∈ rootDomain38) :
    fullColumn m s z/canonRoot38 φ z=
      Complex.I*((1/(Real.pi : ℂ))*p2OmittedRatio38 m ((φ,s),z))/
        stdRoot38 (tauN φ m) (gamma2 φ m) z := by
  have hp' : (φ,z) ∈ a5OmittedRootDomain38 m :=
    ⟨hp.1,fun j _ => rootDomain_avoids38 hp j⟩
  have hD := a5OmittedRoot_ne_zero38 m (φ,z) hp'
  have hS : stdRoot38 (tauN φ m) (gamma2 φ m) z ≠ 0 := by
    have hs := stdRoot_ne_zero38 (lamMinus φ m) (lamPlus φ m) z
      (rootDomain_avoids38 hp m)
    simpa only [add_comm (lamMinus φ m),← tauN_value38 φ hp.1 m,
      ← gamma2_value38 φ hp.1 m] using hs
  rw [a5CanonRoot_omitted_factorization38 m (φ,z) hp]
  unfold fullColumn p2OmittedRatio38 rootFactor38
  field_simp [hD,hS,Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero m),
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,Complex.I_ne_zero]
  ring_nf; simp only [Complex.I_sq]; ring

theorem fullColumn_diagonal_period_mean (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im=0) (m : ℤ) :
    ∃ x ∈ Icc (actualGapLowerAllE02_38 u m) (actualGapUpperAllE02_38 u m),
      abelianPeriod38 m (realSlice u) (fullColumn m s)=
        2*p2OmittedRatio38 m (((realSlice u),s),(x : ℂ)) := by
  let φ : PotPair := realSlice u
  let a : ℝ := actualGapLowerAllE02_38 u m
  let b : ℝ := actualGapUpperAllE02_38 u m
  let G : ℂ → ℂ := fun z => (1/(Real.pi : ℂ))*p2OmittedRatio38 m ((φ,s),z)
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
    analyticOnNhd_const.mul (p2OmittedRatio_own_disc_analytic38 m φ hφ C R hfam s)
  have hGr : ∀ x ∈ Icc a b, (G (x : ℂ)).im=0 := by
    intro x hx
    have hR : (p2OmittedRatio38 m ((φ,s),(x : ℂ))).im=0 :=
      P3JacobianColumns.omittedRatio_real u s hs m x
        (a5OwnClosedBall_omittedDomain38 φ hφ C R hfam m x
          (ball_subset_closedBall (hcut (hseg x hx))))
    dsimp only [G]
    simp only [Complex.mul_im,Complex.div_im,Complex.one_im,Complex.one_re,
      Complex.ofReal_im,hR,mul_zero,zero_mul,sub_zero,zero_div,add_zero]
  have hτ : tauN φ m=((a : ℂ)+b)/2 := by
    rw [tauN_value38 φ hφ m]
    change (lamPlus (realSlice u) m+lamMinus (realSlice u) m)/2 = _
    rw [hends.1,hends.2]
    ring
  have hγ : gamma2 φ m=((b : ℂ)-a)^2 := by
    rw [gamma2_value38 φ hφ m]
    change (lamPlus (realSlice u) m-lamMinus (realSlice u) m)^2 = _
    rw [hends.1,hends.2]
  have hfamily := abelianPeriod_fullfamily_realization38 φ hφ (discC φ) C (discR φ) R
    (isolating_family38 φ hφ) hfam m (fullColumn m s) (fullColumn_entire m s)
  have heq : EqOn (fun z => fullColumn m s z/canonRoot38 φ z)
      (fun z => Complex.I*(G z/S z)) (sphere (C m) (R m)) := by
    intro z hz
    have he := fullColumn_diagonal_div_root m s φ z
      ⟨hφ,fixed_sphere_subset φ C R hfam m hz⟩
    simpa only [G,S,hτ,hγ,mul_div_assoc] using he
  have hperiod : abelianPeriod38 m φ (fullColumn m s)=
      Complex.I*circleIntegral (fun z => G z/S z) (C m) (R m) := by
    unfold abelianPeriod38
    rw [hfamily.2.2,circleIntegral.integral_congr hr.le heq,
      circleIntegral.integral_const_mul]
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
    _ = _ := by
      rw [Complex.I_mul_I]
      dsimp [G,φ]
      field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

theorem fullColumn_gap_point_segment (u : PhysicalL2) (m : ℤ) (x : ℝ)
    (hx : x ∈ Icc (actualGapLowerAllE02_38 u m) (actualGapUpperAllE02_38 u m)) :
    (x : ℂ) ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m) := by
  have hab := (gap_endpoint_levels38 u m).1
  have hi : x ∈ segment ℝ (actualGapLowerAllE02_38 u m)
      (actualGapUpperAllE02_38 u m) := by
    simpa only [segment_eq_Icc hab] using hx
  have himg := image_segment ℝ (Complex.ofRealCLM.toLinearMap.toAffineMap)
    (actualGapLowerAllE02_38 u m) (actualGapUpperAllE02_38 u m)
  rw [(lamPlus_real u m).1,(lamPlus_real u m).2]
  change (Complex.ofRealCLM.toLinearMap.toAffineMap x) ∈
    segment ℝ (Complex.ofRealCLM.toLinearMap.toAffineMap (actualGapLowerAllE02_38 u m))
      (Complex.ofRealCLM.toLinearMap.toAffineMap (actualGapUpperAllE02_38 u m))
  rw [← himg]
  exact ⟨x,hi,rfl⟩

theorem fullColumn_diagonal_period_ne_zero (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im=0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k)) (m : ℤ) :
    abelianPeriod38 m (realSlice u) (fullColumn m s) ≠ 0 := by
  obtain ⟨x,hx,he⟩ := fullColumn_diagonal_period_mean u C R hfam s hs m
  have hxc := fullColumn_gap_point_segment u m x hx
  have hxball : (x : ℂ) ∈ closedBall (C m) (R m) := by
    obtain ⟨c,N,hg,hsp⟩ := hfam
    exact ball_subset_closedBall ((hsp.1 m).1 hxc)
  rw [he]
  exact mul_ne_zero (by norm_num)
    (P3JacobianColumns.omittedRatio_ne_zero (realSlice u) (realSlice_mem_gkW u)
      C R hfam s hσ m x hxball)

theorem fullColumn_diagonal_period_sub_two_bound (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im=0) (m : ℤ) (b : ℝ)
    (hb : ∀ z ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m),
      ‖p2OmittedRatio38 m (((realSlice u),s),z)-1‖ ≤ b) :
    ‖abelianPeriod38 m (realSlice u) (fullColumn m s)-2‖ ≤ 2*b := by
  obtain ⟨x,hx,he⟩ := fullColumn_diagonal_period_mean u C R hfam s hs m
  have h := hb x (fullColumn_gap_point_segment u m x hx)
  rw [he,show 2*p2OmittedRatio38 m (((realSlice u),s),(x : ℂ))-2=
    (2 : ℂ)*(p2OmittedRatio38 m (((realSlice u),s),(x : ℂ))-1) by ring,norm_mul]
  rw [Complex.norm_two]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

end
end NlsGge.GK38.P6FullJacobian
