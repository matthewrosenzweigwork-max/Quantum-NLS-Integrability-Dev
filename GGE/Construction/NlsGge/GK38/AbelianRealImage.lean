import NlsGge.GK38.AbelianZeroGap
import NlsGge.GK38.AbelianHilbert

/-! Prospective actual real images: genuine omitted products FIRST, actual canonical
period and real-only mean value thereafter. No complex mean point is asserted. -/
set_option autoImplicit false
open Set Metric SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

 theorem p2Canonical_period_real38 (m : ℤ) (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) (hfReal : ∀ x : ℝ, (f (x:ℂ)).im=0) :
    CircleIntegrable (fun z => f z/canonRoot38 (realSlice u) z) (C m) (R m) ∧
      (circleIntegral (fun z => f z/canonRoot38 (realSlice u) z) (C m) (R m)).im=0 := by
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
  have hg : AnalyticOnNhd ℂ g (closedBall (C m) (R m)) :=
    (hf.mono (subset_univ _)).div hD hDn
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
    have hfr := hfReal x
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
  obtain ⟨x,hx,hmean⟩ := p2StdRoot_real_mean_value38 a b hab (C m) (R m) hr hcut g hg hgReal
  change (1/(2*(Real.pi:ℂ)*Complex.I))*circleIntegral (fun z => g z/S z) (C m) (R m)=
    -g (x:ℂ) at hmean
  have h2 : 2*(Real.pi:ℂ)*Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hscaled := congrArg (fun w : ℂ => (2*(Real.pi:ℂ)*Complex.I)*w) hmean
  rw [← mul_assoc,mul_one_div_cancel h2,one_mul] at hscaled
  have he : circleIntegral (fun z => f z/canonRoot38 φ z) (C m) (R m) =
      -(Real.pi:ℂ)*(Lib.piN m:ℂ)*g (x:ℂ) := by
    rw [hperiod,hscaled]
    field_simp [Complex.I_ne_zero]
  refine ⟨hci,?_⟩
  rw [he]
  simp only [Complex.mul_im,Complex.neg_im,Complex.ofReal_im,neg_zero,
    Complex.mul_re,zero_mul,mul_zero,add_zero,sub_zero,hgReal x hx]

 theorem p2FullNumerator_real38 (n : ℤ) (s : Lib.L2Seq)
    (hs : ∀ m : ℤ, (s m).im=0) (x : ℝ) : (p2FullNumerator38 n s (x:ℂ)).im=0 := by
  have hfac : ∀ m : ℤ, ((if m=n then 1 else Lib.prodFactor (Lib.sigmaOf s) (x:ℂ) m):ℂ).im=0 := by
    intro m
    by_cases hm : m=n
    · simp only [hm,ite_true,Complex.one_im]
    · simp only [hm,ite_false,Lib.prodFactor,Lib.sigmaOf,Complex.div_im,
        Complex.sub_im,Complex.add_im,Complex.mul_im,Complex.intCast_im,Complex.ofReal_im,hs,
        mul_zero,zero_mul,add_zero,sub_zero,zero_div]
  have hmul := Lib.multipliable_omit n s (x:ℂ)
  have hconj := hmul.map_tprod (starRingEnd ℂ) continuous_star
  have he : (fun m : ℤ => (starRingEnd ℂ)
      (if m=n then 1 else Lib.prodFactor (Lib.sigmaOf s) (x:ℂ) m)) =
      (fun m : ℤ => if m=n then 1 else Lib.prodFactor (Lib.sigmaOf s) (x:ℂ) m) := by
    funext m
    exact Complex.conj_eq_iff_im.mpr (hfac m)
  rw [he] at hconj
  have hp := Complex.conj_eq_iff_im.mp hconj
  have hO : (Lib.omitProd n s (x:ℂ)).im=0 := by
    unfold Lib.omitProd
    simp only [Complex.mul_im,Complex.div_im,Complex.one_im,Complex.ofReal_im,hp,
      mul_zero,zero_mul,sub_zero,add_zero,zero_div]
  have h2 : (-2:ℂ).im=0 := by norm_num
  simp only [p2FullNumerator38,Complex.mul_im,hO,h2,mul_zero,zero_mul,add_zero]

 theorem p2Fn_real38 (n : ℤ) (u : PhysicalL2) (s : P2Space38 n) (hs : p2RealSeq38 n s)
    (m : P2Index38 n) : (p2Fn38 n (realSlice u,s) m).im=0 := by
  have he : ∀ j : ℤ, ((p2Extend38 n s) j).im=0 := by
    intro j
    by_cases hj : j=n
    · subst j
      simp only [p2Extend_self38,Complex.zero_im]
    · simpa only [p2Extend_at38 n s ⟨j,hj⟩] using hs ⟨j,hj⟩
  have hr := p2Canonical_period_real38 m.1 u (discC (realSlice u)) (discR (realSlice u))
    (isolating_family38 (realSlice u) (realSlice_mem_gkW u))
    (p2FullNumerator38 n (p2Extend38 n s)) (p2FullNumerator_entire38 n _)
    (p2FullNumerator_real38 n _ he)
  rw [p2Fn_apply38 n (realSlice u,s) (realSlice_mem_gkW u) m]
  change ((((n-m.1:ℤ):ℂ))*abelianPeriod38 m.1 (realSlice u)
    (p2FullNumerator38 n (p2Extend38 n s))).im=0
  simp only [Complex.mul_im,Complex.intCast_im,zero_mul,add_zero]
  exact mul_eq_zero_of_right _ hr.2

#print axioms p2Canonical_period_real38
#print axioms p2FullNumerator_real38
#print axioms p2Fn_real38
end
end NlsGge.GK38
