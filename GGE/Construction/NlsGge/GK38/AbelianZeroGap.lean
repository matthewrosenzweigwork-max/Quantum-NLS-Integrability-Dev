import NlsGge.GK38.AbelianRealMeanValue
import NlsGge.GK38.AbelianOmittedReality

/-! Actual real zero-in-gap from the canonical contour, including collapsed gaps.
UNCOMPILED prospective source; genuine normalized omitted-root product is used. -/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

 theorem p2Abelian_zero_in_gap38 (m n : ℤ) (_hmn : m ≠ n)
    (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R)
    (U : Set ℂ) (f : ℂ → ℂ) (_hUo : IsOpen U) (hUc : Convex ℝ U)
    (hUs : sphere (C m) (R m) ⊆ U) (hf : AnalyticOnNhd ℂ f U)
    (hfReal : ∀ x : ℝ, (x:ℂ) ∈ segment ℝ (lamMinus (realSlice u) m)
      (lamPlus (realSlice u) m) → (f (x:ℂ)).im=0)
    (hzero : circleIntegral (fun z => f z/canonRoot38 (realSlice u) z) (C m) (R m)=0) :
    ∃ x : ℝ, (x:ℂ) ∈ segment ℝ (lamMinus (realSlice u) m)
      (lamPlus (realSlice u) m) ∧ f (x:ℂ)=0 := by
  let φ : PotPair := realSlice u
  let a : ℝ := actualGapLowerAllE02_38 u m
  let b : ℝ := actualGapUpperAllE02_38 u m
  let D : ℂ → ℂ := fun z => a5OmittedRootProduct38 m (φ,z)
  let S : ℂ → ℂ := stdRoot38 (((a:ℂ)+b)/2) (((b:ℂ)-a)^2)
  let g : ℂ → ℂ := fun z => f z/D z
  have hφ : φ ∈ gkW := realSlice_mem_gkW u
  have hr : 0 < R m := isolating_radius_pos38 hfam m
  have hab : a ≤ b := (gap_endpoint_levels38 u m).1
  have hends := lamPlus_real u m
  have hcut : segment ℝ (a:ℂ) (b:ℂ) ⊆ ball (C m) (R m) := by
    obtain ⟨c,N,hg,hs⟩ := hfam
    simpa only [hends.1,hends.2] using (hs.1 m).1
  have hdom : ∀ z ∈ closedBall (C m) (R m), (φ,z) ∈ a5OmittedRootDomain38 m :=
    fun z hz => a5OwnClosedBall_omittedDomain38 φ hφ C R hfam m z hz
  have hD : AnalyticOnNhd ℂ D (closedBall (C m) (R m)) := by
    intro z hz
    exact (a5OmittedRoot_analytic38 m (φ,z) (hdom z hz)).comp
      (analyticAt_const.prod analyticAt_id)
  have hDn : ∀ z ∈ closedBall (C m) (R m), D z ≠ 0 :=
    fun z hz => a5OmittedRoot_ne_zero38 m (φ,z) (hdom z hz)
  have hfilled := p2ClosedBall_subset_of_sphere38 (C m) (R m) hr.le hUc hUs
  have hg : AnalyticOnNhd ℂ g (closedBall (C m) (R m)) :=
    (hf.mono hfilled).div hD hDn
  have hseg : ∀ x ∈ Icc a b, (x:ℂ) ∈ segment ℝ (a:ℂ) (b:ℂ) := by
    intro x hx
    have hi : x ∈ segment ℝ a b := by simpa only [segment_eq_Icc hab] using hx
    have himg := image_segment ℝ (Complex.ofRealCLM.toLinearMap.toAffineMap) a b
    change (Complex.ofRealCLM.toLinearMap.toAffineMap x) ∈
      segment ℝ (Complex.ofRealCLM.toLinearMap.toAffineMap a)
        (Complex.ofRealCLM.toLinearMap.toAffineMap b)
    rw [← himg]
    exact ⟨x,hi,rfl⟩
  have hgReal : ∀ x ∈ Icc a b, (g (x:ℂ)).im=0 := by
    intro x hx
    have hxc := hcut (hseg x hx)
    have hDr := p2OmittedRoot_real38 m u x (hdom x (ball_subset_closedBall hxc))
    change (D (x:ℂ)).im=0 at hDr
    have hfr := hfReal x (by simpa only [hends.1,hends.2] using hseg x hx)
    dsimp [g]
    simp only [Complex.div_im,hDr,hfr,mul_zero,zero_mul,sub_zero,zero_div]
  have hactual : ∀ z ∈ sphere (C m) (R m),
      canonRoot38 φ z = 2*Complex.I*(S z/(Lib.piN m:ℂ))*D z := by
    intro z hz
    have hroot := a5CanonRoot_omitted_factorization38 m (φ,z)
      ⟨hφ,fixed_sphere_subset φ C R hfam m hz⟩
    have hτ : tauN φ m=((a:ℂ)+b)/2 := by
      rw [tauN_value38 φ hφ m]
      change (lamPlus (realSlice u) m+lamMinus (realSlice u) m)/2=_
      rw [hends.1,hends.2]
      ring
    have hγ : gamma2 φ m=((b:ℂ)-a)^2 := by
      rw [gamma2_value38 φ hφ m]
      change (lamPlus (realSlice u) m-lamMinus (realSlice u) m)^2=_
      rw [hends.1,hends.2]
    simpa only [rootFactor38,hτ,hγ] using hroot
  have hgavg := p2StdRoot_cosine_average38 (a:ℂ) (b:ℂ) (C m) (R m) hr hcut g hg
  have hEq : EqOn (fun z => f z/canonRoot38 φ z)
      (fun z => ((Lib.piN m:ℂ)/(2*Complex.I))*(g z/S z)) (sphere (C m) (R m)) := by
    intro z hz
    have hsn := stdRoot_ne_zero38 (a:ℂ) (b:ℂ) z (by
      intro hzc
      exact (not_lt.mpr (mem_sphere.mp hz).ge) (mem_ball.mp (hcut hzc)))
    change f z/canonRoot38 φ z=((Lib.piN m:ℂ)/(2*Complex.I))*(g z/S z)
    rw [hactual z hz]
    dsimp [g]
    field_simp [Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero m),Complex.I_ne_zero,
      hDn z (sphere_subset_closedBall hz),hsn]
  have hci : CircleIntegrable (fun z => f z/canonRoot38 φ z) (C m) (R m) := by
    apply (circleIntegrable_congr (by simpa only [abs_of_pos hr] using hEq)).mpr
    exact hgavg.1.const_mul _
  have hperiod : circleIntegral (fun z => f z/canonRoot38 φ z) (C m) (R m) =
      ((Lib.piN m:ℂ)/(2*Complex.I))*circleIntegral (fun z => g z/S z) (C m) (R m) := by
    rw [circleIntegral.integral_congr hr.le hEq,circleIntegral.integral_const_mul]
  have hstd : circleIntegral (fun z => g z/S z) (C m) (R m)=0 := by
    rw [hperiod] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left
      (div_ne_zero (Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero m))
        (mul_ne_zero (by norm_num) Complex.I_ne_zero))
  obtain ⟨x,hx,hmean⟩ := p2StdRoot_real_mean_value38 a b hab (C m) (R m) hr hcut g hg hgReal
  have hgzero : g (x:ℂ)=0 := by
    change (1/(2*(Real.pi:ℂ)*Complex.I))*circleIntegral (fun z => g z/S z) (C m) (R m)=_ at hmean
    rw [hstd,mul_zero] at hmean
    exact neg_eq_zero.mp hmean.symm
  refine ⟨x,?_,?_⟩
  · simpa only [hends.1,hends.2] using hseg x hx
  · exact (div_eq_zero_iff.mp hgzero).resolve_right
      (hDn x (ball_subset_closedBall (hcut (hseg x hx))))

#print axioms p2Abelian_zero_in_gap38
end
end NlsGge.GK38
