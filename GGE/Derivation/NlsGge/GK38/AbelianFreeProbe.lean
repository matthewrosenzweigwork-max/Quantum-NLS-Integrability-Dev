import NlsGge.GK38.AbelianContractProbe
import NlsGge.GK38.IsolatingRealProbe

/-! Prospective genuine full-Fn free normalization regression. All complex amplitudes,
all signed omitted/excited/output labels; the missing coordinate is truly omitted. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.P2FreeProbe
noncomputable section

theorem criticalShift_zero : a5CriticalShift38 (0:PotPair)=0 := by
  apply Subtype.ext
  funext m
  change a5CriticalShift38 0 m=0
  rw [a5CriticalShift_value38 0 free_mem_gkW m,lamDot_zero38]
  simp only [countingCenter38,sub_self]

 theorem ratio_excited (j : ℤ) (t z : ℂ) (hp : ((0:PotPair),z) ∈ a5OmittedRootDomain38 j) :
    p2OmittedRatio38 j ((0,t • lp.single 2 j (1:ℂ)),z)=1 := by
  have hO : Lib.omitProd j (t • lp.single 2 j (1:ℂ)) z=Lib.omitProd j 0 z := by
    simpa only [zero_add] using Lib.omitProd_add_single j 0 z t
  have hD := a5CriticalNumerator_free38 j z
  rw [a5CriticalNumerator38,criticalShift_zero] at hD
  unfold p2OmittedRatio38
  rw [hO,← hD]
  exact div_self (by rw [hD]; exact a5OmittedRoot_ne_zero38 j _ hp)

/-- The raw Abelian periods give the book's diagonal2, not diagonal1 or2pi. -/
theorem full_coordinate_single (n j m : ℤ) (hjn : j ≠ n) (hmn : m ≠ n) (t : ℂ) :
    (((n-m:ℤ):ℂ))*abelianPeriod38 m 0
      (p2FullNumerator38 n (t • lp.single 2 j (1:ℂ))) = if m=j then 2*t else 0 := by
  let s : Lib.L2Seq := t • lp.single 2 j (1:ℂ)
  let C : ℤ → ℂ := countingCenter38
  let R : ℤ → ℝ := fun _ => Real.pi/4
  have hfam : IsolatingFamily38 (0:PotPair) C R := isolating_free_family_probe38
  obtain ⟨c,N,hgeom,_hspec⟩ := isolating_free_family_probe38
  have hσn : Lib.sigmaOf s n=C n := by
    simp only [Lib.sigmaOf,s,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 j (1:ℂ) (Ne.symm hjn),mul_zero,add_zero,C,countingCenter38]
  have hnball : Lib.sigmaOf s n ∈ closedBall (C n) (R n) := by
    rw [hσn]
    exact mem_closedBall_self (by dsimp [R]; positivity)
  have hd (z : ℂ) (hz : z ∈ closedBall (C m) (R m)) :=
    (p2OwnSigma_denominator38 C R c N hgeom n m (Ne.symm hmn) s hnball z hz).1
  let G : ℂ → ℂ := fun z => Complex.I*(((n-m:ℤ):ℂ))*(Lib.sigmaOf s m-z)*
    p2OmittedRatio38 m ((0,s),z)/(Lib.sigmaOf s n-z)
  have hG : AnalyticOnNhd ℂ G (closedBall (C m) (R m)) := by
    exact (((analyticOnNhd_const.mul (analyticOnNhd_const.sub analyticOnNhd_id)).mul
      (p2OmittedRatio_own_disc_analytic38 m 0 free_mem_gkW C R hfam s))).div
      (analyticOnNhd_const.sub analyticOnNhd_id) hd
  have hcut : segment ℝ (lamMinus (0:PotPair) m) (lamPlus 0 m) ⊆ ball (C m) (R m) := by
    rw [lamMinus_zero38,lamPlus_zero38,segment_same]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact mem_ball_self (by dsimp [R]; positivity)
  have ha := p2StdRoot_cosine_average38 (C m) (C m) (C m) (R m)
    (by dsimp [R]; positivity) (by simpa only [lamMinus_zero38,lamPlus_zero38] using hcut) G hG
  have hfamily := abelianPeriod_fullfamily_realization38 0 free_mem_gkW
    (discC 0) C (discR 0) R (isolating_family38 0 free_mem_gkW) hfam m
    (p2FullNumerator38 n s) (p2FullNumerator_entire38 n s)
  have hEq : EqOn (fun z => (((n-m:ℤ):ℂ))*(p2FullNumerator38 n s z/canonRoot38 0 z))
      (fun z => G z/stdRoot38 (C m) 0 z) (sphere (C m) (R m)) := by
    intro z hz
    change (((n-m:ℤ):ℂ))*(p2FullNumerator38 n s z/canonRoot38 0 z)=_
    rw [p2FullNumerator_div_root38 n m s 0 z
      ⟨free_mem_gkW,fixed_sphere_subset 0 C R hfam m hz⟩ (hd z (sphere_subset_closedBall hz))]
    have hτ : tauN (0:PotPair) m=C m := by
      rw [tauN_value38 0 free_mem_gkW m,lamPlus_zero38,lamMinus_zero38]
      dsimp [C]
      ring
    have hγ : gamma2 (0:PotPair) m=0 := by
      rw [gamma2_value38 0 free_mem_gkW m,lamPlus_zero38,lamMinus_zero38,sub_self]
      norm_num
    rw [hτ,hγ]
    dsimp [G,C]
    ring
  have hperiod : (((n-m:ℤ):ℂ))*abelianPeriod38 m 0 (p2FullNumerator38 n s)=
      -(2*(Real.pi:ℂ)*Complex.I)*G (C m) := by
    unfold abelianPeriod38
    rw [hfamily.2.2,← circleIntegral.integral_const_mul,
      circleIntegral.integral_congr (by dsimp [R]; positivity) hEq]
    have he := ha.2.2
    have hmid : (C m+C m)/2=C m := by ring
    rw [hmid] at he
    simp only [sub_self,zero_div,zero_mul,add_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),
      intervalIntegral.integral_const,sub_zero,Complex.real_smul] at he
    rw [he]
    push_cast
    ring
  rw [hperiod]
  by_cases hmj : m=j
  · subst m
    have hp : ((0:PotPair),C j) ∈ a5OmittedRootDomain38 j := a5OmittedRoot_free_center_mem38 j
    have hR := ratio_excited j t (C j) hp
    have hσj : Lib.sigmaOf s j-C j=t := by simp [Lib.sigmaOf,s,C,countingCenter38]
    have hdj : C n-C j ≠ 0 := by rw [← hσn]; exact hd (C j) (mem_closedBall_self (by dsimp [R]; positivity))
    simp only [ite_true]
    dsimp [G]
    rw [hσj,hR,hσn]
    dsimp [C,countingCenter38] at *
    have he : (n:ℂ)*(Real.pi:ℂ)-(j:ℂ)*(Real.pi:ℂ)=(((n-j:ℤ):ℂ))*(Real.pi:ℂ) := by push_cast; ring
    rw [he] at hdj ⊢
    field_simp [hdj]
    simp [Complex.I_sq]
  · have hσm : Lib.sigmaOf s m-C m=0 := by
      simp only [Lib.sigmaOf,s,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
        lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 j (1:ℂ) hmj,mul_zero,add_zero,C,countingCenter38,sub_self]
    simp only [hmj,ite_false]
    dsimp [G]
    rw [hσm]
    ring

 theorem extend_restrict_of_zero (n : ℤ) (s : Lib.L2Seq) (hs : s n=0) :
    p2Extend38 n (p2Restrict38 n s)=s := by
  apply Subtype.ext
  funext m
  change p2Extend38 n (p2Restrict38 n s) m=s m
  by_cases hm : m=n
  · subst m
    rw [p2Extend_self38,hs]
  · rw [p2Extend_at38 n _ ⟨m,hm⟩,p2Restrict_apply38]

 theorem actual_Fn_single (n j : ℤ) (hjn : j ≠ n) (t : ℂ) (m : P2Index38 n) :
    p2Fn38 n (0,p2Restrict38 n (t • lp.single 2 j (1:ℂ))) m =
      if m.1=j then 2*t else 0 := by
  have hgraph := p2Fn_apply38 n
    ((0:PotPair),p2Restrict38 n (t • lp.single 2 j (1:ℂ))) free_mem_gkW m
  have hs0 : (t • lp.single 2 j (1:ℂ) : Lib.L2Seq) n=0 := by
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 j (1:ℂ) (Ne.symm hjn),mul_zero]
  have hnum : p2Numerator38 n (p2Restrict38 n (t • lp.single 2 j (1:ℂ)))=
      p2FullNumerator38 n (t • lp.single 2 j (1:ℂ)) :=
    congrArg (p2FullNumerator38 n) (extend_restrict_of_zero n _ hs0)
  apply hgraph.trans
  simpa only [p2FnCoord38,hnum] using full_coordinate_single n j m.1 hjn m.2 t

#print axioms full_coordinate_single
#print axioms actual_Fn_single
end
end NlsGge.GK38.P2FreeProbe
