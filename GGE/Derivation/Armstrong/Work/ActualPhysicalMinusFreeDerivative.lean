import Armstrong.Work.ActualCartesianFreePrefactor
import Armstrong.Work.ActualScalarCartesianModels
import Armstrong.Work.RawBetaSourceSum
import NlsGge.GK38.XiSqFinalProbe
import NlsGge.GK38.XiCommonDomain
import Armstrong.Frozen.RawBetaAnalytic.gkSourceBeta_characterization38
import Mathlib.Tactic.Ring

set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- The literal physical-minus scalar expression has the reflected Fourier
differential on every independent complex potential direction. The original
W/F and supplied analytic source-sum V/beta are retained. No global physical
map, real-valued X/Y, Poisson or canonicity conclusion is asserted. -/
theorem gk16_same_family_physical_minus_at_zero_derivative38
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
    (n : ℤ) :
    DifferentiableAt ℂ
      (fun phi : PotPair => (xiN38 n phi/2) *
        (gk16ActualScalarZMinus38 F n phi *
          Complex.exp (-Complex.I*beta n phi))) 0 ∧
    ∀ h : PotPair,
      (fderiv ℂ
        (fun phi : PotPair => (xiN38 n phi/2) *
          (gk16ActualScalarZMinus38 F n phi *
            Complex.exp (-Complex.I*beta n phi)))
        (0 : PotPair)) h = -physicalFourier h.1 (-n) := by
  classical
  have hzeroV : (0 : PotPair) ∈ V := by
    simpa only [realSlice_zero] using hrealV (mem_range_self (0 : PhysicalL2))
  have hzeroW : (0 : PotPair) ∈ W := hVW hzeroV
  have hzeroGK : (0 : PotPair) ∈ gkW := hWgk hzeroW
  let phi0 : {chi : PotPair // chi ∈ W} := ⟨0,hzeroW⟩
  obtain ⟨_hsourceSummable,hbetaSource⟩ := hbeta n phi0 hzeroV
  have hbetaTerm (m : P2Index38 n) :
      gkSourceBeta38 W hWopen hreal hWgk F
        hFanalytic hFn hperiod n m.1 m.2 phi0=0 := by
    apply (gkSourceBeta_characterization38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod n m.1 m.2 phi0).2.2
    left
    change muSeq 0 m.1=lamMinus 0 m.1
    rw [muSeq_zero38,lamMinus_zero38]
  have hbeta0 : beta n (0 : PotPair)=0 := by
    rw [hbetaSource]
    calc
      (∑' m : P2Index38 n,
        gkSourceBeta38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m.1 m.2 phi0) =
          ∑' _m : P2Index38 n, (0 : ℂ) := tsum_congr hbetaTerm
      _ = 0 := tsum_zero
  have hH0 : gk16TerminalRoot38 n (0 : PotPair)=0 := by
    simp [gk16TerminalRoot38,antiDiscrim,monodromyPair_zero_potential,freeE]
  have htau0 : tauN (0 : PotPair) n=muSeq 0 n := by
    rw [tauN_value38 0 hzeroGK n,lamPlus_zero38,lamMinus_zero38,muSeq_zero38]
    ring
  let C : PotPair → ℂ := fun phi => tauN phi n-muSeq phi n-gk16TerminalRoot38 n phi
  have hcore := gk16_minus_prefactor_at_zero_derivative38 n
  have hC : HasFDerivAt C (fderiv ℂ C 0) 0 := hcore.1.hasFDerivAt
  have hC0 : C (0 : PotPair)=0 := by
    dsimp [C]
    rw [htau0,hH0,sub_self,sub_zero]
  let E : PotPair → ℂ := fun phi =>
    gk16TerminalRoot38 n phi *
      gk16OwnCorrectionCoefficient38 phi n (p2Extend38 n (F n phi))
        (discC phi n) (discR phi n) (muSeq phi n)
  obtain ⟨delta,hdelta,_hdeltaW,_hfixed,hcharts⟩ :=
    gk16_same_family_actual_correction_chart38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal (0 : PhysicalL2)
  obtain ⟨_S,_hS,_hSspec,_hjoint,_heq,hEchart⟩ := hcharts n
  have hEanalytic : AnalyticAt ℂ E 0 := by
    apply hEchart 0
    simpa only [realSlice_zero] using
      (mem_ball_self hdelta : realSlice (0 : PhysicalL2) ∈
        ball (realSlice (0 : PhysicalL2)) delta)
  have hE0 : E (0 : PotPair)=0 := by
    dsimp [E]
    rw [hH0,zero_mul]
  let U : PotPair → ℂ := fun phi => Complex.exp (E phi)
  have hU : HasFDerivAt U (fderiv ℂ U 0) 0 :=
    hEanalytic.cexp.differentiableAt.hasFDerivAt
  have hU0 : U (0 : PotPair)=1 := by
    simp only [U,hE0,Complex.exp_zero]
  have hZeq : gk16ActualScalarZMinus38 F n=
      fun phi : PotPair => (2*C phi)*U phi := by
    funext phi
    change (2*(tauN phi n-muSeq phi n)-2*gk16TerminalRoot38 n phi)*
      Complex.exp (E phi)=(2*C phi)*Complex.exp (E phi)
    congr 1
    dsimp [C]
    ring
  have hZproduct := (hC.const_mul (2 : ℂ)).mul hU
  have hZ := hZproduct.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun phi => congrFun hZeq phi))
  have hZ0 : gk16ActualScalarZMinus38 F n (0 : PotPair)=0 := by
    rw [hZeq]
    change (2*C (0 : PotPair))*U 0=0
    rw [hC0]
    simp only [mul_zero,zero_mul]
  have hZvalue (h : PotPair) :
      (fderiv ℂ (gk16ActualScalarZMinus38 F n) 0) h=
        -2*physicalFourier h.1 (-n) := by
    rw [hZ.fderiv]
    change (2*C (0 : PotPair))*(fderiv ℂ U 0) h+
      U 0*(2*(fderiv ℂ C 0) h)=_
    have hCvalue : (fderiv ℂ C 0) h=-physicalFourier h.1 (-n) := hcore.2 h
    rw [hC0,hU0,hCvalue]
    ring
  have hZcanonical : HasFDerivAt (gk16ActualScalarZMinus38 F n)
      (fderiv ℂ (gk16ActualScalarZMinus38 F n) 0) 0 :=
    hZ.differentiableAt.hasFDerivAt
  have hxi0 : xiN38 n (0 : PotPair)=1 := A5FinalFixture.canonical_sqrt_free_one n
  have hxiAt : AnalyticAt ℂ (xiN38 n) 0 := by
    apply xiN38_analytic_commonDomain n 0
    simpa only [realSlice_zero] using realSlice_mem_xiCommonDomain38 (0 : PhysicalL2)
  let X : PotPair → ℂ := fun phi => xiN38 n phi/2
  have hXanalytic : AnalyticAt ℂ X 0 := hxiAt.div_const
  have hX : HasFDerivAt X (fderiv ℂ X 0) 0 := hXanalytic.differentiableAt.hasFDerivAt
  have hX0 : X (0 : PotPair)=(1 : ℂ)/2 := by
    simp only [X,hxi0]
  let B : PotPair → ℂ := fun phi => Complex.exp (-Complex.I*beta n phi)
  have hBanalytic : AnalyticAt ℂ B 0 :=
    ((analyticAt_const (v := -Complex.I)).mul (hbetaAnalytic n 0 hzeroV)).cexp
  have hB : HasFDerivAt B (fderiv ℂ B 0) 0 := hBanalytic.differentiableAt.hasFDerivAt
  have hB0 : B (0 : PotPair)=1 := by
    simp only [B,hbeta0,mul_zero,Complex.exp_zero]
  have hfinal := hX.mul (hZcanonical.mul hB)
  change HasFDerivAt
    (fun phi : PotPair => (xiN38 n phi/2) *
      (gk16ActualScalarZMinus38 F n phi *
        Complex.exp (-Complex.I*beta n phi)))
    (X 0 • (gk16ActualScalarZMinus38 F n 0 • fderiv ℂ B 0 +
      B 0 • fderiv ℂ (gk16ActualScalarZMinus38 F n) 0) +
      (gk16ActualScalarZMinus38 F n * B) 0 • fderiv ℂ X 0)
    (0 : PotPair) at hfinal
  refine ⟨hfinal.differentiableAt,?_⟩
  intro h
  rw [hfinal.fderiv]
  change X (0 : PotPair)*
    (gk16ActualScalarZMinus38 F n 0*(fderiv ℂ B 0) h+
      B 0*(fderiv ℂ (gk16ActualScalarZMinus38 F n) 0) h)+
      (gk16ActualScalarZMinus38 F n 0*B 0)*(fderiv ℂ X 0) h=_
  rw [hX0,hZ0,hB0,hZvalue]
  ring

end
end NlsGge.GK38
