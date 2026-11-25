import NlsGge.GK38.AngleRegularFactor
import NlsGge.GK38.AngleCollapsedDirichletSeparation
import NlsGge.GK38.AbelianStdRootAverage
import NlsGge.GK38.AbelianJacobianGeometry

/-! Source-only actual complex cosine centering identities. These are genuine
period identities, not an assumed P7 input family or a complex mean-value
point. They prepare the quadratic collapsed-root estimate. -/
set_option autoImplicit false
open Set Metric MeasureTheory
namespace NlsGge.GK38
noncomputable section

theorem angleRegularFactor_own_disc_analytic38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (n m : ℤ) (hnm : n ≠ m) (s : Lib.L2Seq)
    (hσ : Lib.sigmaOf s n ∈ closedBall (C n) (R n)) :
    AnalyticOnNhd ℂ (fun z => angleRegularFactor38 n m ((φ,s),z))
      (closedBall (C m) (R m)) := by
  intro z hz
  exact (angleRegularFactor_joint_own_disc38 n m hnm φ hφ C R hfam s hσ z hz).comp
    (analyticAt_const.prod analyticAt_id)

theorem angleRegularFactor_own_disc_ne_zero38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (n m : ℤ) (hnm : n ≠ m) (s : Lib.L2Seq)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (z : ℂ) (hz : z ∈ closedBall (C m) (R m)) :
    angleRegularFactor38 n m ((φ,s),z) ≠ 0 := by
  obtain ⟨c,N,hg,hsp⟩ := hfam
  exact div_ne_zero
    (mul_ne_zero Complex.I_ne_zero
      (P3JacobianColumns.omittedRatio_ne_zero φ hφ C R ⟨c,N,hg,hsp⟩ s hσ m z hz))
    (p2OwnSigma_denominator38 C R c N hg n m hnm s (hσ n) z hz).1

theorem angleActual_period_cosine38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (n m : ℤ) (hnm : n ≠ m) (s : Lib.L2Seq)
    (hσ : Lib.sigmaOf s n ∈ closedBall (C n) (R n)) :
    let x : ℝ → ℂ := fun θ => (lamMinus φ m+lamPlus φ m)/2+
      ((lamPlus φ m-lamMinus φ m)/2)*(Real.cos θ : ℂ)
    IntervalIntegrable (fun θ : ℝ => (Lib.sigmaOf s m-x θ)*
      angleRegularFactor38 n m ((φ,s),x θ)) volume 0 (2*Real.pi) ∧
    abelianPeriod38 m φ (p2FullNumerator38 n s) = -Complex.I*
      (∫ θ : ℝ in (0 : ℝ)..2*Real.pi, (Lib.sigmaOf s m-x θ)*
        angleRegularFactor38 n m ((φ,s),x θ)) := by
  let G : ℂ → ℂ := fun z => (Lib.sigmaOf s m-z)*angleRegularFactor38 n m ((φ,s),z)
  let S : ℂ → ℂ := stdRoot38 ((lamMinus φ m+lamPlus φ m)/2)
    ((lamPlus φ m-lamMinus φ m)^2)
  have hr : 0 < R m := isolating_radius_pos38 hfam m
  have hcut : segment ℝ (lamMinus φ m) (lamPlus φ m) ⊆ ball (C m) (R m) := by
    obtain ⟨c,N,hg,hsp⟩ := hfam
    exact (hsp.1 m).1
  have hG : AnalyticOnNhd ℂ G (closedBall (C m) (R m)) :=
    (analyticOnNhd_const.sub analyticOnNhd_id).mul
      (angleRegularFactor_own_disc_analytic38 φ hφ C R hfam n m hnm s hσ)
  have hτ : tauN φ m=(lamMinus φ m+lamPlus φ m)/2 := by
    rw [tauN_value38 φ hφ m]
    ring
  have hγ := gamma2_value38 φ hφ m
  have havg := p2StdRoot_cosine_average38 (lamMinus φ m) (lamPlus φ m)
    (C m) (R m) hr hcut G hG
  have hEq : EqOn (fun z => p2FullNumerator38 n s z/canonRoot38 φ z)
      (fun z => G z/S z) (sphere (C m) (R m)) := by
    intro z hz
    obtain ⟨c,N,hg,hsp⟩ := hfam
    have hden := (p2OwnSigma_denominator38 C R c N hg n m hnm s hσ z
      (sphere_subset_closedBall hz)).1
    change p2FullNumerator38 n s z/canonRoot38 φ z=G z/S z
    rw [angleRegularFactor_factorization38 n m s φ z
      ⟨hφ,fixed_sphere_subset φ C R ⟨c,N,hg,hsp⟩ m hz⟩ hden,hτ,hγ]
    dsimp only [G,S]
    ring
  have hfamily := abelianPeriod_fullfamily_realization38 φ hφ (discC φ) C (discR φ) R
    (isolating_family38 φ hφ) hfam m (p2FullNumerator38 n s) (p2FullNumerator_entire38 n s)
  refine ⟨havg.2.1,?_⟩
  unfold abelianPeriod38
  rw [hfamily.2.2,circleIntegral.integral_congr hr.le hEq]
  exact havg.2.2

/-- The actual zero-period equation centers the root against the actual
regular-factor cosine average. Both averages are genuinely integrable before
linearity. A later lower-bound/Taylor argument is still needed for O(gamma²). -/
theorem angleActual_zero_period_centering38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (n m : ℤ) (hnm : n ≠ m) (s : Lib.L2Seq)
    (hσ : Lib.sigmaOf s n ∈ closedBall (C n) (R n))
    (hzero : abelianPeriod38 m φ (p2FullNumerator38 n s)=0) :
    let x : ℝ → ℂ := fun θ => (lamMinus φ m+lamPlus φ m)/2+
      ((lamPlus φ m-lamMinus φ m)/2)*(Real.cos θ : ℂ)
    IntervalIntegrable (fun θ : ℝ => angleRegularFactor38 n m ((φ,s),x θ))
      volume 0 (2*Real.pi) ∧
    IntervalIntegrable (fun θ : ℝ => (Real.cos θ : ℂ)*
      angleRegularFactor38 n m ((φ,s),x θ)) volume 0 (2*Real.pi) ∧
    (Lib.sigmaOf s m-tauN φ m)*
      (∫ θ : ℝ in (0 : ℝ)..2*Real.pi, angleRegularFactor38 n m ((φ,s),x θ)) =
      ((lamPlus φ m-lamMinus φ m)/2)*
        (∫ θ : ℝ in (0 : ℝ)..2*Real.pi, (Real.cos θ : ℂ)*
          angleRegularFactor38 n m ((φ,s),x θ)) := by
  let x : ℝ → ℂ := fun θ => (lamMinus φ m+lamPlus φ m)/2+
    ((lamPlus φ m-lamMinus φ m)/2)*(Real.cos θ : ℂ)
  let Z : ℝ → ℂ := fun θ => angleRegularFactor38 n m ((φ,s),x θ)
  have ha := angleRegularFactor_own_disc_analytic38 φ hφ C R hfam n m hnm s hσ
  have hpath (θ : ℝ) : x θ ∈ closedBall (C m) (R m) := by
    obtain ⟨c,N,hg,hsp⟩ := hfam
    exact ball_subset_closedBall ((hsp.1 m).1
      (p2Cosine_mem_segment38 (lamMinus φ m) (lamPlus φ m) θ))
  have hcont : Continuous Z := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (ha (x θ) (hpath θ)).continuousAt.comp
      (by fun_prop : ContinuousAt x θ)
  have hi0 : IntervalIntegrable Z volume 0 (2*Real.pi) := hcont.intervalIntegrable _ _
  have hi1 : IntervalIntegrable (fun θ : ℝ => (Real.cos θ : ℂ)*Z θ) volume 0 (2*Real.pi) :=
    ((Complex.continuous_ofReal.comp Real.continuous_cos).mul hcont).intervalIntegrable _ _
  have hp := (angleActual_period_cosine38 φ hφ C R hfam n m hnm s hσ).2
  rw [hp] at hzero
  have hI0 := (mul_eq_zero.mp hzero).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
  have hτ : tauN φ m=(lamMinus φ m+lamPlus φ m)/2 := by
    rw [tauN_value38 φ hφ m]
    ring
  have he (θ : ℝ) : (Lib.sigmaOf s m-x θ)*Z θ=
      (Lib.sigmaOf s m-tauN φ m)*Z θ-
        ((lamPlus φ m-lamMinus φ m)/2)*((Real.cos θ : ℂ)*Z θ) := by
    dsimp only [x]
    rw [hτ]
    ring
  have hcenter :
      (∫ θ : ℝ in (0 : ℝ)..2*Real.pi, (Lib.sigmaOf s m-x θ)*Z θ)=
      (Lib.sigmaOf s m-tauN φ m)*(∫ θ : ℝ in (0 : ℝ)..2*Real.pi, Z θ)-
        ((lamPlus φ m-lamMinus φ m)/2)*
          (∫ θ : ℝ in (0 : ℝ)..2*Real.pi, (Real.cos θ : ℂ)*Z θ) := by
    simp_rw [he]
    rw [intervalIntegral.integral_sub (hi0.const_mul _) (hi1.const_mul _),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  refine ⟨hi0,hi1,?_⟩
  apply sub_eq_zero.mp
  rw [← hcenter]
  exact hI0

end
end NlsGge.GK38
