import Armstrong.Work.ActualPhysicalMinusRealAnalytic
import Armstrong.Work.ActualPhysicalMinusFreeDerivative
import NlsGge.Sobolev.PeriodicBridge
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem gk19_same_family_minus_physical_zero_fourier38
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
          Complex.exp (-Complex.I*beta n (realSlice u)))) :
    HasFDerivAt Phi
        (reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)
        (0 : PhysicalL2) ∧
      fderiv ℝ Phi (0 : PhysicalL2) =
        reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ ∧
      (∀ (h : PhysicalL2) (n : ℤ),
        (fderiv ℝ Phi (0 : PhysicalL2) h) n = -physicalFourier h (-n)) ∧
      (fderiv ℝ Phi (0 : PhysicalL2)).IsInvertible := by
  have hPhiAnalytic : AnalyticAt ℝ Phi (0 : PhysicalL2) :=
    gk16_same_family_minus_physical_real_analytic38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal V hVopen hrealV hVW beta hbeta hXY
      Phi hcoords (0 : PhysicalL2)
  have hPhi : HasFDerivAt Phi (fderiv ℝ Phi (0 : PhysicalL2))
      (0 : PhysicalL2) := hPhiAnalytic.differentiableAt.hasFDerivAt
  have hCoeff (h : PhysicalL2) (n : ℤ) :
      (fderiv ℝ Phi (0 : PhysicalL2) h) n = -physicalFourier h (-n) := by
    let f : PotPair → ℂ := fun phi => (xiN38 n phi/2) *
      (gk16ActualScalarZMinus38 F n phi *
        Complex.exp (-Complex.I*beta n phi))
    obtain ⟨hfDiff,hfValue⟩ :=
      gk16_same_family_physical_minus_at_zero_derivative38 W hWopen hreal hWgk F
        hFanalytic hFn hFinv hperiod hFreal V hVopen hrealV hVW beta hbeta
        hbetaAnalytic n
    have hfC : HasFDerivAt f (fderiv ℂ f (0 : PotPair))
        (0 : PotPair) := hfDiff.hasFDerivAt
    have hfR : HasFDerivAt f
        ((fderiv ℂ f (0 : PotPair)).restrictScalars ℝ)
        (realSlice (0 : PhysicalL2)) := by
      rw [realSlice_zero]
      exact hfC.restrictScalars ℝ
    have hSlice : HasFDerivAt
        (fun u : PhysicalL2 => f (realSlice u))
        (((fderiv ℂ f (0 : PotPair)).restrictScalars ℝ).comp realSlice)
        (0 : PhysicalL2) :=
      HasFDerivAt.comp (𝕜 := ℝ) (g := f) (f := realSlice)
        (0 : PhysicalL2) hfR realSlice.hasFDerivAt
    let ev : Lib.L2Z →L[ℝ] ℂ := lp.evalCLM ℝ (fun _ : ℤ => ℂ) 2 n
    have hEval : HasFDerivAt (fun u : PhysicalL2 => Phi u n)
        (ev.comp (fderiv ℝ Phi (0 : PhysicalL2))) (0 : PhysicalL2) :=
      HasFDerivAt.comp (𝕜 := ℝ) (g := ev) (f := Phi)
        (0 : PhysicalL2) ev.hasFDerivAt hPhi
    have hEvalSame : HasFDerivAt
        (fun u : PhysicalL2 => f (realSlice u))
        (ev.comp (fderiv ℝ Phi (0 : PhysicalL2))) (0 : PhysicalL2) :=
      hEval.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun u => (hcoords u n).symm))
    have hDeriv : ev.comp (fderiv ℝ Phi (0 : PhysicalL2)) =
        ((fderiv ℂ f (0 : PotPair)).restrictScalars ℝ).comp realSlice :=
      hEvalSame.unique hSlice
    have hValue := DFunLike.congr_fun hDeriv h
    change (fderiv ℝ Phi (0 : PhysicalL2) h) n =
      (fderiv ℂ f (0 : PotPair)) (realSlice h) at hValue
    calc
      (fderiv ℝ Phi (0 : PhysicalL2) h) n =
          (fderiv ℂ f (0 : PotPair)) (realSlice h) := hValue
      _ = -physicalFourier (realSlice h).1 (-n) := hfValue (realSlice h)
      _ = -physicalFourier h (-n) := by rw [realSlice_fst]
  let A : PhysicalL2 →L[ℝ] Lib.L2Z :=
    reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have hD : fderiv ℝ Phi (0 : PhysicalL2) = A := by
    apply ContinuousLinearMap.ext
    intro h
    apply lp.ext
    funext n
    change (fderiv ℝ Phi (0 : PhysicalL2) h) n = reflectedFourierL2 h n
    calc
      (fderiv ℝ Phi (0 : PhysicalL2) h) n = -physicalFourier h (-n) := hCoeff h n
      _ = reflectedFourierL2 h n := by
        rw [reflectedFourierL2_apply]
        rfl
  have hAt : HasFDerivAt Phi A (0 : PhysicalL2) := by
    rw [← hD]
    exact hPhi
  let B : Lib.L2Z →L[ℝ] PhysicalL2 :=
    reflectedFourierL2.toContinuousLinearEquiv.symm.toContinuousLinearMap.restrictScalars ℝ
  have hAB : A.comp B = ContinuousLinearMap.id ℝ Lib.L2Z := by
    apply ContinuousLinearMap.ext
    intro z
    change reflectedFourierL2 (reflectedFourierL2.symm z) = z
    exact reflectedFourierL2.apply_symm_apply z
  have hBA : B.comp A = ContinuousLinearMap.id ℝ PhysicalL2 := by
    apply ContinuousLinearMap.ext
    intro u
    change reflectedFourierL2.symm (reflectedFourierL2 u) = u
    exact reflectedFourierL2.symm_apply_apply u
  have hInverse : A.IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse hAB hBA
  refine ⟨hAt,hD,hCoeff,?_⟩
  rw [hD]
  exact hInverse

end
end NlsGge.GK38
