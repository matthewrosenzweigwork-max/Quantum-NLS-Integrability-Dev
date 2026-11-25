import Armstrong.Work.ActualPhysicalMinusFourierLinearization
import Armstrong.Work.ActualPhysicalActionMass
import NlsGge.GK38.Lib.ProperLocalHomeo

/- The supplied SAME physical Phi has a real-analytic local chart at zero.
Its zero value comes from the already earned full mass norm identity; actual
map analyticity and derivative invertibility come from REALAN and D054.
Only local source/target inverse properties are asserted. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem gk19_same_family_minus_physical_local_chart38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi,F n phi) = 0)
    (hFinv : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (phi,y))
        (F n phi)).IsInvertible)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2*(Real.pi : ℂ) else 0)
    (hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t)
    (V : Set PotPair) (hVopen : IsOpen V)
    (hrealV : range realSlice ⊆ V) (hVW : V ⊆ W)
    (beta : ℤ → PotPair → ℂ)
    (hbeta : ∀ n : ℤ, ∀ phi : {chi : PotPair // chi ∈ W}, phi.1 ∈ V →
      Summable (fun m : P2Index38 n =>
        ‖gkSourceBeta38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m.1 m.2 phi‖) ∧
      beta n phi.1 = (∑' m : P2Index38 n,
          gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi))
    (hbetaAnalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (beta n) V)
    (hXY : ∀ n : ℤ,
      AnalyticOnNhd ℂ (gk16ScalarXModel38 F beta n) V ∧
      AnalyticOnNhd ℂ (gk16ScalarYModel38 F beta n) V)
    (Phi : PhysicalL2 → Lib.L2Z)
    (hcoords : ∀ (u : PhysicalL2) (n : ℤ),
      Phi u n = (xiN38 n (realSlice u)/2) *
        (gk16ActualScalarZMinus38 F n (realSlice u) *
          Complex.exp (-Complex.I*beta n (realSlice u))))
    (hNormSq : ∀ u : PhysicalL2, ‖Phi u‖ ^ 2 = ‖u‖ ^ 2) :
    ∃ e : OpenPartialHomeomorph PhysicalL2 Lib.L2Z,
      (0 : PhysicalL2) ∈ e.source ∧
      (0 : Lib.L2Z) ∈ e.target ∧
      (⇑e = Phi) ∧
      e (0 : PhysicalL2) = 0 ∧
      AnalyticAt ℝ e.symm (0 : Lib.L2Z) := by
  have hPhiZero : Phi (0 : PhysicalL2) = 0 := by
    have hNormZero : ‖Phi (0 : PhysicalL2)‖ ^ 2 = 0 := by
      simpa only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        hNormSq (0 : PhysicalL2)
    exact lp.norm_eq_zero_iff.mp (sq_eq_zero_iff.mp hNormZero)
  have hAnalytic : AnalyticAt ℝ Phi (0 : PhysicalL2) :=
    gk16_same_family_minus_physical_real_analytic38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal V hVopen hrealV hVW beta hbeta hXY
      Phi hcoords (0 : PhysicalL2)
  have hD0 := gk19_same_family_minus_physical_zero_fourier38 W hWopen hreal hWgk F
    hFanalytic hFn hFinv hperiod hFreal V hVopen hrealV hVW beta hbeta
    hbetaAnalytic hXY Phi hcoords
  obtain ⟨e,heSource,hePhi,heInverse⟩ :=
    Lib.exists_analytic_chart (f := Phi) (x := (0 : PhysicalL2))
      hAnalytic hD0.2.2.2
  have heZero : e (0 : PhysicalL2) = 0 :=
    (congrFun hePhi (0 : PhysicalL2)).trans hPhiZero
  have heTarget : (0 : Lib.L2Z) ∈ e.target := by
    simpa only [heZero] using e.map_source heSource
  refine ⟨e,heSource,heTarget,hePhi,heZero,?_⟩
  simpa only [hPhiZero] using heInverse

end
end NlsGge.GK38
