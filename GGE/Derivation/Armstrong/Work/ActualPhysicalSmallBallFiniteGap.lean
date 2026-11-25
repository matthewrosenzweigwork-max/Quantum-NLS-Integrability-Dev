import Armstrong.Work.ActualPhysicalMinusFourierLinearization
import Armstrong.Work.ActualPhysicalActionMass
import Armstrong.Work.ActualPhysicalLocalChart
import Armstrong.Work.ActualLocalFiniteGapDensity
import NlsGge.GK38.AbelianPsiTheorem141
import NlsGge.GK38.Lib.ProperLocalHomeo

/- Actual same-Phi physical small-ball finite-gap producer.
The one p6/T2/MASS Phi and the same L0 chart are retained. The full norm-square
identity earns norm preservation; one radius below both chart radii identifies
the genuine chart-ball preimage with a newly chosen physical norm ball. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem a7_actual_physical_small_ball_finite_gap_producer065 :
    ∃ W : Set PotPair,
    ∃ hWopen : IsOpen W,
    ∃ hreal : range realSlice ⊆ W,
    ∃ hWgk : W ⊆ gkW,
    ∃ F : (n : ℤ) → PotPair → P2Space38 n,
    ∃ hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W,
    ∃ hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → p2Fn38 n (phi,F n phi) = 0,
    ∃ hFinv : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (phi,y)) (F n phi)).IsInvertible,
    ∃ hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2*(Real.pi : ℂ) else 0,
    ∃ hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t,
    ∃ V : Set PotPair, ∃ beta : ℤ → PotPair → ℂ,
      IsOpen V ∧ range realSlice ⊆ V ∧ V ⊆ W ∧ V ⊆ xiCommonDomain38 ∧
      (∀ n : ℤ, ∀ phi : {chi : PotPair // chi ∈ W}, phi.1 ∈ V →
        Summable (fun m : P2Index38 n =>
          ‖gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi‖) ∧
        beta n phi.1 = ∑' m : P2Index38 n,
          gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi) ∧
      (∀ n : ℤ,
        AnalyticOnNhd ℂ (gk16ScalarXModel38 F beta n) V ∧
        AnalyticOnNhd ℂ (gk16ScalarYModel38 F beta n) V) ∧
      ∃ Phi : PhysicalL2 → Lib.L2Z,
        Continuous Phi ∧
        (∀ (u : PhysicalL2) (n : ℤ),
          Phi u n = (xiN38 n (realSlice u)/2) *
            (gk16ActualScalarZMinus38 F n (realSlice u) *
              Complex.exp (-Complex.I*beta n (realSlice u)))) ∧
        (∀ (u : PhysicalL2) (n : ℤ),
          ‖Phi u n‖ ^ 2 = actualGapActionAllE02_38 u n) ∧
        (∀ u : PhysicalL2,
          HasSum (fun n : ℤ => actualGapActionAllE02_38 u n) (‖u‖ ^ 2) ∧
          ‖Phi u‖ ^ 2 = ‖u‖ ^ 2) ∧
        (∀ u : PhysicalL2, AnalyticAt ℝ Phi u) ∧
        HasFDerivAt Phi
          (reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)
          (0 : PhysicalL2) ∧
        fderiv ℝ Phi (0 : PhysicalL2) =
          reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ ∧
        (∀ (h : PhysicalL2) (n : ℤ),
          (fderiv ℝ Phi (0 : PhysicalL2) h) n = -physicalFourier h (-n)) ∧
        (fderiv ℝ Phi (0 : PhysicalL2)).IsInvertible ∧
        ∃ e : OpenPartialHomeomorph PhysicalL2 Lib.L2Z,
          (0 : PhysicalL2) ∈ e.source ∧
          (0 : Lib.L2Z) ∈ e.target ∧
          (⇑e = Phi) ∧
          e (0 : PhysicalL2) = 0 ∧
          AnalyticAt ℝ e.symm (0 : Lib.L2Z) ∧
          ∃ δ : ℝ, 0 < δ ∧
            Metric.ball (0 : PhysicalL2) δ ⊆ e.source ∧
            Metric.ball (0 : Lib.L2Z) δ ⊆ e.target ∧
            (e.source ∩ Phi ⁻¹' Metric.ball (0 : Lib.L2Z) δ) = Metric.ball (0 : PhysicalL2) δ ∧
            Metric.ball (0 : PhysicalL2) δ ⊆
              closure (Metric.ball (0 : PhysicalL2) δ ∩
                {u : PhysicalL2 |
                  {n : ℤ | actualGapLowerAllE02_38 u n <
                    actualGapUpperAllE02_38 u n}.Finite})

:= by
  obtain ⟨W,hWopen,hreal,hWgk,F,hFanalytic,_hjoint,_hroots,
    hspec,hrealspec,_hfree,_hmass⟩ := p6Actual_psi_theorem141_same_family38
  have hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi,F n phi) = 0 :=
    fun n phi hphi => (hspec n phi hphi).1
  have hFinv : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (phi,y)) (F n phi)).IsInvertible :=
    fun n phi hphi => (hspec n phi hphi).2.1
  have hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2*(Real.pi : ℂ) else 0 :=
    fun n phi hphi => (hspec n phi hphi).2.2.2.2.1
  have hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t := by
    intro n u
    obtain ⟨t,ht,hzero,hbase,_hroots⟩ := hrealspec n u
    exact ⟨t,ht,hzero,hbase⟩
  obtain ⟨V,beta,hVopen,hrealV,hVW,hVxi,hbeta,hbetaAnalytic,hXY⟩ :=
    gk16_same_family_xy_scalar_models38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal
  refine ⟨W,hWopen,hreal,hWgk,F,hFanalytic,hFn,hFinv,hperiod,hFreal,V,beta,
    hVopen,hrealV,hVW,hVxi,hbeta,hXY,?_⟩
  obtain ⟨Phi,hPhi,hcoords,hAction,hMass⟩ :=
    gk16_same_family_minus_physical_action_mass38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal V hVopen hrealV hVW beta hbeta hXY
  have hRealAnalytic : ∀ u : PhysicalL2, AnalyticAt ℝ Phi u :=
    gk16_same_family_minus_physical_real_analytic38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal V hVopen hrealV hVW beta hbeta hXY
      Phi hcoords
  have hD0 := gk19_same_family_minus_physical_zero_fourier38 W hWopen hreal hWgk F
    hFanalytic hFn hFinv hperiod hFreal V hVopen hrealV hVW beta hbeta
    hbetaAnalytic hXY Phi hcoords
  have hNormSq : ∀ u : PhysicalL2, ‖Phi u‖ ^ 2 = ‖u‖ ^ 2 :=
    fun u => (hMass u).2
  have hChart := gk19_same_family_minus_physical_local_chart38 W hWopen hreal hWgk F
    hFanalytic hFn hFinv hperiod hFreal V hVopen hrealV hVW beta hbeta
    hbetaAnalytic hXY Phi hcoords hNormSq
  obtain ⟨e,heSource,heTarget,heForward,heZero,heInvAnalytic⟩ := hChart
  have hNorm : ∀ u : PhysicalL2, ‖Phi u‖ = ‖u‖ := by
    intro u
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hNormSq u)
  obtain ⟨r,hr,hsourceBall⟩ := Metric.isOpen_iff.mp e.open_source 0 heSource
  obtain ⟨s,hs,htargetBall⟩ := Metric.isOpen_iff.mp e.open_target 0 heTarget
  let δ : ℝ := min r s
  have hδ : 0 < δ := lt_min hr hs
  have hphysicalBall : Metric.ball (0 : PhysicalL2) δ ⊆ e.source := by
    intro u hu
    exact hsourceBall (Metric.ball_subset_ball (min_le_left r s) hu)
  have htargetBall' : Metric.ball (0 : Lib.L2Z) δ ⊆ e.target := by
    intro z hz
    exact htargetBall (Metric.ball_subset_ball (min_le_right r s) hz)
  have hpreimage : Phi ⁻¹' Metric.ball (0 : Lib.L2Z) δ =
      Metric.ball (0 : PhysicalL2) δ := by
    ext u
    change dist (Phi u) 0 < δ ↔ dist u 0 < δ
    simp only [dist_zero_right, hNorm]
  have hU : e.source ∩ Phi ⁻¹' Metric.ball (0 : Lib.L2Z) δ =
      Metric.ball (0 : PhysicalL2) δ := by
    ext u
    change (u ∈ e.source ∧ u ∈ Phi ⁻¹' Metric.ball (0 : Lib.L2Z) δ) ↔
      u ∈ Metric.ball (0 : PhysicalL2) δ
    rw [hpreimage]
    constructor
    · exact fun ⟨_, hu⟩ => hu
    · intro hu
      exact ⟨hphysicalBall hu, hu⟩
  have hFD := gk19_actual_finite_gap_dense_on_chart_ball38
    Phi hAction e heForward δ hδ htargetBall'
  have hchartExtended :
      (0 : PhysicalL2) ∈ e.source ∧
      (0 : Lib.L2Z) ∈ e.target ∧
      (⇑e = Phi) ∧
      e (0 : PhysicalL2) = 0 ∧
      AnalyticAt ℝ e.symm (0 : Lib.L2Z) ∧
      ∃ δ : ℝ, 0 < δ ∧
        Metric.ball (0 : PhysicalL2) δ ⊆ e.source ∧
        Metric.ball (0 : Lib.L2Z) δ ⊆ e.target ∧
        (e.source ∩ Phi ⁻¹' Metric.ball (0 : Lib.L2Z) δ) =
          Metric.ball (0 : PhysicalL2) δ ∧
        Metric.ball (0 : PhysicalL2) δ ⊆
          closure (Metric.ball (0 : PhysicalL2) δ ∩
            {u : PhysicalL2 |
              {n : ℤ | actualGapLowerAllE02_38 u n <
                actualGapUpperAllE02_38 u n}.Finite}) := by
    refine ⟨heSource,heTarget,heForward,heZero,heInvAnalytic,δ,hδ,
      hphysicalBall,htargetBall',hU,?_⟩
    simpa only [← hU] using hFD.2.2
  exact ⟨Phi,hPhi,hcoords,hAction,hMass,hRealAnalytic,
    hD0.1,hD0.2.1,hD0.2.2.1,hD0.2.2.2,⟨e,hchartExtended⟩⟩


end
end NlsGge.GK38
