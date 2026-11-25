import Armstrong.Work.ActualScalarCartesianModels
import Armstrong.Work.RawBetaUniformSourceBound
import Armstrong.Work.ActualWeightedCorrectionBound
import NlsGge.GK38.XiCommonDomain
import NlsGge.GK38.TauGammaL2Realization

/-!
# Actual scalar Cartesian models and outer-index square summability

SPECULATIVE_PARENT_UNACCEPTED, task XY_OUTER_L2_IMPLEMENTATION_012.
Exact independently reviewed two literal definitions and four target signatures.
One original W/F and one earned V/beta are retained. Every quantitative witness
is earned independently before all varying complex potentials and signed modes.
No actual Hilbert/global map, realtrace or inverse is defined here.
-/

set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- Ordinary direct plus/minus scalar assembly; source meaning only on the
returned common domain where beta is the convergent original-W source sum. -/
def gk16ScalarXModel38
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (beta : ℤ → PotPair → ℂ) (n : ℤ) (phi : PotPair) : ℂ :=
  (xiN38 n phi / (Real.sqrt 8 : ℂ)) *
    (gk16ActualScalarZPlus38 F n phi * Complex.exp (Complex.I * beta n phi) +
      gk16ActualScalarZMinus38 F n phi * Complex.exp (-Complex.I * beta n phi))

/-- Literal sqrt(8)*i denominator, with the same F and beta representative. -/
def gk16ScalarYModel38
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (beta : ℤ → PotPair → ℂ) (n : ℤ) (phi : PotPair) : ℂ :=
  (xiN38 n phi / ((Real.sqrt 8 : ℂ) * Complex.I)) *
    (gk16ActualScalarZPlus38 F n phi * Complex.exp (Complex.I * beta n phi) -
      gk16ActualScalarZMinus38 F n phi * Complex.exp (-Complex.I * beta n phi))

/-- XY-012-SOURCE: any genuine noncollapsed path value gives the exact
GK theta=eta+beta formulas. Convergence/equality of beta is an earned source
series prerequisite, discharged jointly by XY-012-ANALYTIC below. -/
theorem gk16_xy_models_of_original_path38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi,F n phi) = 0)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2*(Real.pi : ℂ) else 0)
    (beta : ℤ → PotPair → ℂ)
    (n : ℤ) (phi : {chi : PotPair // chi ∈ W})
    (hbeta :
      Summable (fun m : P2Index38 n =>
        ‖gkSourceBeta38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m.1 m.2 phi‖) ∧
      beta n phi.1 = (∑' m : P2Index38 n,
          gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi))
    (hgap : lamMinus phi.1 n ≠ lamPlus phi.1 n)
    (p : GKRootedPiecewisePath38 ⟨phi.1,hWgk phi.2⟩ n)
    (eta : ℂ)
    (heta : HasGKImproperPathIntegral38 n n F
      ⟨phi.1,hWgk phi.2⟩ p eta) :
    gk16ScalarXModel38 F beta n phi.1 =
      (xiN38 n phi.1 / (Real.sqrt 8 : ℂ)) *
        ((lamPlus phi.1 n-lamMinus phi.1 n) *
            Complex.exp (Complex.I * (eta + (∑' m : P2Index38 n,
          gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi))) +
          (lamPlus phi.1 n-lamMinus phi.1 n) *
            Complex.exp (-Complex.I * (eta + (∑' m : P2Index38 n,
          gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi)))) ∧
    gk16ScalarYModel38 F beta n phi.1 =
      (xiN38 n phi.1 / ((Real.sqrt 8 : ℂ) * Complex.I)) *
        ((lamPlus phi.1 n-lamMinus phi.1 n) *
            Complex.exp (Complex.I * (eta + (∑' m : P2Index38 n,
          gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi))) -
          (lamPlus phi.1 n-lamMinus phi.1 n) *
            Complex.exp (-Complex.I * (eta + (∑' m : P2Index38 n,
          gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi)))) := by
  obtain ⟨hplus,hminus⟩ :=
    gk16_actual_scalar_models_of_path_integral38 W hWgk F hperiod
      n phi hgap p eta heta
  constructor <;>
    simp only [gk16ScalarXModel38,gk16ScalarYModel38,hplus,hminus,hbeta.2,
      mul_assoc,← Complex.exp_add,← mul_add]

/-- XY-012-ANALYTIC: one original-F beta representative and one common
open source domain before all signed modes. Direct models are analytic through
all complex collapsed gaps; no additive eta at collapse is postulated. -/
theorem gk16_same_family_xy_scalar_models38
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
    : ∃ V : Set PotPair, ∃ beta : ℤ → PotPair → ℂ,
      IsOpen V ∧ range realSlice ⊆ V ∧ V ⊆ W ∧ V ⊆ xiCommonDomain38 ∧
      (∀ n : ℤ, ∀ phi : {chi : PotPair // chi ∈ W}, phi.1 ∈ V →
        Summable (fun m : P2Index38 n =>
          ‖gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi‖) ∧
        beta n phi.1 = (∑' m : P2Index38 n,
          gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi)) ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (beta n) V) ∧
      ∀ n : ℤ,
        AnalyticOnNhd ℂ (gk16ScalarXModel38 F beta n) V ∧
        AnalyticOnNhd ℂ (gk16ScalarYModel38 F beta n) V := by
  classical
  obtain ⟨Ws,hWs,hrealS,hWsW,hrows,_huniform,⟨beta,hbetaAnalytic,hbetaSource⟩,_hdecay⟩ :=
    gk151_source_beta_series38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal
  let D : Set PotPair := {phi | ∃ u : PhysicalL2, ∃ delta : ℝ,
    0 < delta ∧ ball (realSlice u) delta ⊆ W ∧
      (∀ n : ℤ,
        AnalyticOnNhd ℂ (gk16ActualScalarZPlus38 F n) (ball (realSlice u) delta) ∧
        AnalyticOnNhd ℂ (gk16ActualScalarZMinus38 F n) (ball (realSlice u) delta)) ∧
      phi ∈ ball (realSlice u) delta}
  have hDopen : IsOpen D := by
    apply isOpen_iff_mem_nhds.mpr
    intro phi hphi
    obtain ⟨u,delta,hdelta,hsub,hZ,hphiBall⟩ := hphi
    exact Filter.mem_of_superset (isOpen_ball.mem_nhds hphiBall)
      (fun psi hpsi => ⟨u,delta,hdelta,hsub,hZ,hpsi⟩)
  have hrealD : range realSlice ⊆ D := by
    rintro phi ⟨u,rfl⟩
    obtain ⟨delta,hdelta,hsub,hZ⟩ :=
      gk16_same_family_scalar_models_analytic38 W hWopen hreal hWgk F
        hFanalytic hFn hFinv hperiod hFreal u
    exact ⟨u,delta,hdelta,hsub,hZ,mem_ball_self hdelta⟩
  let V : Set PotPair := (Ws ∩ xiCommonDomain38) ∩ D
  have hVopen : IsOpen V := (hWs.inter isOpen_xiCommonDomain38).inter hDopen
  have hrealV : range realSlice ⊆ V := by
    rintro phi ⟨u,rfl⟩
    exact ⟨⟨hrealS (mem_range_self u),realSlice_mem_xiCommonDomain38 u⟩,
      hrealD (mem_range_self u)⟩
  have hVW : V ⊆ W := fun phi hphi => hWsW hphi.1.1
  have hVxi : V ⊆ xiCommonDomain38 := fun phi hphi => hphi.1.2
  have hbetaV (n : ℤ) : AnalyticOnNhd ℂ (beta n) V :=
    (hbetaAnalytic n).mono (fun phi hphi => hphi.1.1)
  have hZV (n : ℤ) :
      AnalyticOnNhd ℂ (gk16ActualScalarZPlus38 F n) V ∧
      AnalyticOnNhd ℂ (gk16ActualScalarZMinus38 F n) V := by
    constructor
    · intro phi hphi
      obtain ⟨u,delta,_hdelta,_hsub,hZ,hphiBall⟩ := hphi.2
      exact (hZ n).1 phi hphiBall
    · intro phi hphi
      obtain ⟨u,delta,_hdelta,_hsub,hZ,hphiBall⟩ := hphi.2
      exact (hZ n).2 phi hphiBall
  refine ⟨V,beta,hVopen,hrealV,hVW,hVxi,?_,hbetaV,?_⟩
  · intro n phi hphi
    exact ⟨hrows n phi hphi.1.1,hbetaSource n phi hphi.1.1⟩
  · intro n
    have hxi : AnalyticOnNhd ℂ (xiN38 n) V :=
      (xiN38_analytic_commonDomain n).mono hVxi
    have hxiX : AnalyticOnNhd ℂ
        (fun phi => xiN38 n phi / (Real.sqrt 8 : ℂ)) V := hxi.div_const
    have hxiY : AnalyticOnNhd ℂ
        (fun phi => xiN38 n phi / ((Real.sqrt 8 : ℂ)*Complex.I)) V := hxi.div_const
    have hplus : AnalyticOnNhd ℂ
        (fun phi => gk16ActualScalarZPlus38 F n phi *
          Complex.exp (Complex.I * beta n phi)) V :=
      (hZV n).1.mul (((analyticOnNhd_const (v := Complex.I)).mul (hbetaV n)).cexp)
    have hminus : AnalyticOnNhd ℂ
        (fun phi => gk16ActualScalarZMinus38 F n phi *
          Complex.exp (-Complex.I * beta n phi)) V :=
      (hZV n).2.mul (((analyticOnNhd_const (v := -Complex.I)).mul (hbetaV n)).cexp)
    constructor
    · change AnalyticOnNhd ℂ
        (fun phi : PotPair => (xiN38 n phi / (Real.sqrt 8 : ℂ)) *
          (gk16ActualScalarZPlus38 F n phi * Complex.exp (Complex.I * beta n phi) +
            gk16ActualScalarZMinus38 F n phi * Complex.exp (-Complex.I * beta n phi))) V
      exact hxiX.mul (hplus.add hminus)
    · change AnalyticOnNhd ℂ
        (fun phi : PotPair => (xiN38 n phi / ((Real.sqrt 8 : ℂ)*Complex.I)) *
          (gk16ActualScalarZPlus38 F n phi * Complex.exp (Complex.I * beta n phi) -
            gk16ActualScalarZMinus38 F n phi * Complex.exp (-Complex.I * beta n phi))) V
      exact hxiY.mul (hplus.sub hminus)

/-- OUTERL2-012-BOUND: no coordinate bound is assumed. All constants
precede varying complex potentials and all signed modes. M is a fresh actual
spectral square-mass witness; hidden mass witnesses from beta/K/xi stay separate.
The proof must earn both coordinate Summable facts before using their tsums. -/
theorem gk16_same_family_xy_outer_l2_bound38
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
    (u : PhysicalL2) :
    ∃ delta b0 K X M : ℝ,
      0 < delta ∧ 0 ≤ b0 ∧ 0 ≤ K ∧ 0 ≤ X ∧ 0 ≤ M ∧
      ball (realSlice u) delta ⊆ V ∩ xiCommonDomain38 ∧
      ∀ phi : {chi : PotPair // chi ∈ W}, phi.1 ∈ ball (realSlice u) delta →
        (∀ n : ℤ, ‖xiN38 n phi.1‖ ≤ X) ∧
        (∀ n : ℤ,
          ‖Complex.exp (Complex.I * beta n phi.1)‖ ≤ Real.exp b0 ∧
          ‖Complex.exp (-Complex.I * beta n phi.1)‖ ≤ Real.exp b0) ∧
        (∀ n : ℤ,
          ‖gk16TerminalRoot38 n phi.1 *
            gk16OwnCorrectionCoefficient38 phi.1 n
              (p2Extend38 n (F n phi.1)) (discC phi.1 n) (discR phi.1 n)
              (muSeq phi.1 n)‖ ≤ K) ∧
        Summable (fun n : ℤ => ‖gk151BetaMass38 phi.1 n‖^2) ∧
        (∑' n : ℤ, ‖gk151BetaMass38 phi.1 n‖^2) ≤ M ∧
        (∀ n : ℤ,
          ‖gk16ScalarXModel38 F beta n phi.1‖^2 ≤
            8 * X^2 * Real.exp (2*(K+b0)) * ‖gk151BetaMass38 phi.1 n‖^2 ∧
          ‖gk16ScalarYModel38 F beta n phi.1‖^2 ≤
            8 * X^2 * Real.exp (2*(K+b0)) * ‖gk151BetaMass38 phi.1 n‖^2) ∧
        Summable (fun n : ℤ => ‖gk16ScalarXModel38 F beta n phi.1‖^2) ∧
        Summable (fun n : ℤ => ‖gk16ScalarYModel38 F beta n phi.1‖^2) ∧
        (∑' n : ℤ, ‖gk16ScalarXModel38 F beta n phi.1‖^2) ≤
          8 * X^2 * Real.exp (2*(K+b0)) * M ∧
        (∑' n : ℤ, ‖gk16ScalarYModel38 F beta n phi.1‖^2) ≤
          8 * X^2 * Real.exp (2*(K+b0)) * M := by
  classical
  have huGK : realSlice u ∈ gkW := hWgk (hreal (mem_range_self u))
  obtain ⟨Wb,hWb,hrealB,_hWbW,hbetaLocal⟩ :=
    gk151_source_beta_exponential_local_bound38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal
  obtain ⟨Vb,b0,hVb,huVb,_hVbWb,hb0,hbetaBound⟩ :=
    hbetaLocal (realSlice u) (hrealB (mem_range_self u))
  obtain ⟨rK,K,hrK,hK,_hKW,hweightedBound⟩ :=
    gk16_same_family_actual_weighted_correction_bound38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal u
  obtain ⟨Um,hUm,_hUmW,M,hM,hmass⟩ :=
    gk151BetaMass_local_l2_38 (realSlice u) huGK
  obtain ⟨Ux,hUx,c,hxiMass⟩ := xiN38_l2_near_one (realSlice u) huGK
  let X : ℝ := Real.sqrt (max c 0)+1
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hmax : 0 ≤ max c 0 := le_max_right _ _
  have hxiBound (phi : PotPair) (hphi : phi ∈ Ux) (n : ℤ) :
      ‖xiN38 n phi‖ ≤ X := by
    obtain ⟨hsum,hbound⟩ := hxiMass phi hphi
    have hterm : ‖xiN38 n phi-1‖^2 ≤ ∑' m : ℤ, ‖xiN38 m phi-1‖^2 := by
      simpa only [Finset.sum_singleton] using
        hsum.sum_le_tsum ({n} : Finset ℤ) (fun _ _ => sq_nonneg _)
    have hpoint : ‖xiN38 n phi-1‖^2 ≤ max c 0 :=
      hterm.trans (hbound.trans (le_max_left _ _))
    have herr : ‖xiN38 n phi-1‖ ≤ Real.sqrt (max c 0) := by
      nlinarith only [hpoint,Real.sq_sqrt hmax,norm_nonneg (xiN38 n phi-1),
        Real.sqrt_nonneg (max c 0)]
    calc
      ‖xiN38 n phi‖ ≤ ‖xiN38 n phi-1‖+‖(1 : ℂ)‖ :=
        norm_le_norm_sub_add (xiN38 n phi) 1
      _ ≤ Real.sqrt (max c 0)+1 := add_le_add herr (by simp only [norm_one,le_refl])
      _ = X := rfl
  let T : Set PotPair := V ∩ (xiCommonDomain38 ∩
    (Vb ∩ (ball (realSlice u) rK ∩ (Um ∩ Ux))))
  have hT : T ∈ 𝓝 (realSlice u) :=
    inter_mem (hVopen.mem_nhds (hrealV (mem_range_self u)))
      (inter_mem (isOpen_xiCommonDomain38.mem_nhds (realSlice_mem_xiCommonDomain38 u))
        (inter_mem (hVb.mem_nhds huVb)
          (inter_mem (isOpen_ball.mem_nhds (mem_ball_self hrK)) (inter_mem hUm hUx))))
  obtain ⟨delta,hdelta,hdeltaT⟩ := Metric.mem_nhds_iff.mp hT
  have hdeltaV : ball (realSlice u) delta ⊆ V ∩ xiCommonDomain38 :=
    fun phi hphi => ⟨(hdeltaT hphi).1,(hdeltaT hphi).2.1⟩
  let C : ℝ := 8*X^2*Real.exp (2*(K+b0))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsqrt : 0 < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtSq : (Real.sqrt 8)^2 = 8 := Real.sq_sqrt (by norm_num)
  have hnormSqrt : ‖(Real.sqrt 8 : ℂ)‖ = Real.sqrt 8 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hsqrt]
  refine ⟨delta,b0,K,X,M,hdelta,hb0,hK,hX,hM,hdeltaV,?_⟩
  intro phi hphi
  have hphiT := hdeltaT hphi
  have hphiV : phi.1 ∈ V := hphiT.1
  have hphiB : phi.1 ∈ Vb := hphiT.2.2.1
  have hphiK : phi.1 ∈ ball (realSlice u) rK := hphiT.2.2.2.1
  have hphiM : phi.1 ∈ Um := hphiT.2.2.2.2.1
  have hphiX : phi.1 ∈ Ux := hphiT.2.2.2.2.2
  have hphiGK : phi.1 ∈ gkW := hWgk phi.2
  have hxi (n : ℤ) : ‖xiN38 n phi.1‖ ≤ X := hxiBound phi.1 hphiX n
  have hexpBeta (n : ℤ) :
      ‖Complex.exp (Complex.I*beta n phi.1)‖ ≤ Real.exp b0 ∧
      ‖Complex.exp (-Complex.I*beta n phi.1)‖ ≤ Real.exp b0 := by
    have h := hbetaBound phi hphiB n
    rw [← (hbeta n phi hphiV).2] at h
    exact h
  have hweighted (n : ℤ) :
      ‖gk16TerminalRoot38 n phi.1 *
        gk16OwnCorrectionCoefficient38 phi.1 n (p2Extend38 n (F n phi.1))
          (discC phi.1 n) (discR phi.1 n) (muSeq phi.1 n)‖ ≤ K :=
    hweightedBound phi.1 hphiK n
  obtain ⟨hmassSum,hmassBound⟩ := hmass phi.1 hphiM
  have hpoint (n : ℤ) :
      ‖gk16ScalarXModel38 F beta n phi.1‖^2 ≤ C*‖gk151BetaMass38 phi.1 n‖^2 ∧
      ‖gk16ScalarYModel38 F beta n phi.1‖^2 ≤ C*‖gk151BetaMass38 phi.1 n‖^2 := by
    let a : ℝ := ‖gk151BetaMass38 phi.1 n‖
    have ha : 0 ≤ a := norm_nonneg _
    have hgamma : Real.sqrt ‖gamma2 phi.1 n‖ =
        ‖lamPlus phi.1 n-lamMinus phi.1 n‖ := by
      rw [gamma2_value38 phi.1 hphiGK n,norm_pow,Real.sqrt_sq (norm_nonneg _)]
    have hpref := gk16_terminal_prefactors_norm38 n phi.1 hphiGK
    rw [hgamma] at hpref
    have hPplus : ‖2*(tauN phi.1 n-muSeq phi.1 n)+2*gk16TerminalRoot38 n phi.1‖ ≤
        4*a := by
      dsimp [a]
      rw [norm_gk151BetaMass38]
      linarith only [hpref.1,norm_nonneg (lamPlus phi.1 n-lamMinus phi.1 n)]
    have hPminus : ‖2*(tauN phi.1 n-muSeq phi.1 n)-2*gk16TerminalRoot38 n phi.1‖ ≤
        4*a := by
      dsimp [a]
      rw [norm_gk151BetaMass38]
      linarith only [hpref.2,norm_nonneg (lamPlus phi.1 n-lamMinus phi.1 n)]
    let w : ℂ := gk16TerminalRoot38 n phi.1 *
      gk16OwnCorrectionCoefficient38 phi.1 n (p2Extend38 n (F n phi.1))
        (discC phi.1 n) (discR phi.1 n) (muSeq phi.1 n)
    have hw : ‖w‖ ≤ K := hweighted n
    have hew : ‖Complex.exp w‖ ≤ Real.exp K :=
      (Complex.norm_exp_le_exp_norm w).trans (Real.exp_le_exp.mpr hw)
    have henegw : ‖Complex.exp (-w)‖ ≤ Real.exp K :=
      (Complex.norm_exp_le_exp_norm (-w)).trans
        (Real.exp_le_exp.mpr (by simpa only [norm_neg] using hw))
    have hZplus : ‖gk16ActualScalarZPlus38 F n phi.1‖ ≤ 4*Real.exp K*a := by
      calc
        ‖gk16ActualScalarZPlus38 F n phi.1‖ =
            ‖2*(tauN phi.1 n-muSeq phi.1 n)+2*gk16TerminalRoot38 n phi.1‖ *
              ‖Complex.exp (-w)‖ := by
          change ‖(2*(tauN phi.1 n-muSeq phi.1 n)+2*gk16TerminalRoot38 n phi.1) *
            Complex.exp (-w)‖ = _
          exact norm_mul _ _
        _ ≤ (4*a)*Real.exp K :=
          mul_le_mul hPplus henegw (norm_nonneg _) (mul_nonneg (by norm_num) ha)
        _ = 4*Real.exp K*a := by ring
    have hZminus : ‖gk16ActualScalarZMinus38 F n phi.1‖ ≤ 4*Real.exp K*a := by
      calc
        ‖gk16ActualScalarZMinus38 F n phi.1‖ =
            ‖2*(tauN phi.1 n-muSeq phi.1 n)-2*gk16TerminalRoot38 n phi.1‖ *
              ‖Complex.exp w‖ := by
          change ‖(2*(tauN phi.1 n-muSeq phi.1 n)-2*gk16TerminalRoot38 n phi.1) *
            Complex.exp w‖ = _
          exact norm_mul _ _
        _ ≤ (4*a)*Real.exp K :=
          mul_le_mul hPminus hew (norm_nonneg _) (mul_nonneg (by norm_num) ha)
        _ = 4*Real.exp K*a := by ring
    let E : ℝ := Real.exp (K+b0)
    let Aplus : ℂ := gk16ActualScalarZPlus38 F n phi.1 *
      Complex.exp (Complex.I*beta n phi.1)
    let Aminus : ℂ := gk16ActualScalarZMinus38 F n phi.1 *
      Complex.exp (-Complex.I*beta n phi.1)
    have hAplus : ‖Aplus‖ ≤ 4*E*a := by
      calc
        ‖Aplus‖ = ‖gk16ActualScalarZPlus38 F n phi.1‖ *
            ‖Complex.exp (Complex.I*beta n phi.1)‖ := norm_mul _ _
        _ ≤ (4*Real.exp K*a)*Real.exp b0 :=
          mul_le_mul hZplus (hexpBeta n).1 (norm_nonneg _)
            (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos K).le) ha)
        _ = 4*E*a := by dsimp [E]; rw [Real.exp_add]; ring
    have hAminus : ‖Aminus‖ ≤ 4*E*a := by
      calc
        ‖Aminus‖ = ‖gk16ActualScalarZMinus38 F n phi.1‖ *
            ‖Complex.exp (-Complex.I*beta n phi.1)‖ := norm_mul _ _
        _ ≤ (4*Real.exp K*a)*Real.exp b0 :=
          mul_le_mul hZminus (hexpBeta n).2 (norm_nonneg _)
            (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos K).le) ha)
        _ = 4*E*a := by dsimp [E]; rw [Real.exp_add]; ring
    have hsum : ‖Aplus+Aminus‖ ≤ 8*E*a := by
      have h := norm_add_le Aplus Aminus
      linarith only [h,hAplus,hAminus]
    have hdiff : ‖Aplus-Aminus‖ ≤ 8*E*a := by
      have h := norm_sub_le Aplus Aminus
      linarith only [h,hAplus,hAminus]
    have hquot : 0 ≤ X/Real.sqrt 8 := div_nonneg hX hsqrt.le
    have hXnorm : ‖gk16ScalarXModel38 F beta n phi.1‖ ≤
        (X/Real.sqrt 8)*(8*E*a) := by
      calc
        ‖gk16ScalarXModel38 F beta n phi.1‖ =
            (‖xiN38 n phi.1‖/Real.sqrt 8)*‖Aplus+Aminus‖ := by
          change ‖(xiN38 n phi.1/(Real.sqrt 8 : ℂ))*(Aplus+Aminus)‖ = _
          rw [norm_mul,norm_div,hnormSqrt]
        _ ≤ (X/Real.sqrt 8)*(8*E*a) :=
          mul_le_mul (div_le_div_of_nonneg_right (hxi n) hsqrt.le) hsum
            (norm_nonneg _) hquot
    have hYnorm : ‖gk16ScalarYModel38 F beta n phi.1‖ ≤
        (X/Real.sqrt 8)*(8*E*a) := by
      calc
        ‖gk16ScalarYModel38 F beta n phi.1‖ =
            (‖xiN38 n phi.1‖/Real.sqrt 8)*‖Aplus-Aminus‖ := by
          change ‖(xiN38 n phi.1/((Real.sqrt 8 : ℂ)*Complex.I))*(Aplus-Aminus)‖ = _
          rw [norm_mul,norm_div,norm_mul,hnormSqrt,Complex.norm_I,mul_one]
        _ ≤ (X/Real.sqrt 8)*(8*E*a) :=
          mul_le_mul (div_le_div_of_nonneg_right (hxi n) hsqrt.le) hdiff
            (norm_nonneg _) hquot
    have hEsq : E^2 = Real.exp (2*(K+b0)) := by
      dsimp [E]
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    have halgebra : ((X/Real.sqrt 8)*(8*E*a))^2 = C*a^2 := by
      dsimp [C]
      simp only [mul_pow,div_pow,hsqrtSq,hEsq]
      ring
    have hsquareX := pow_le_pow_left₀
      (norm_nonneg (gk16ScalarXModel38 F beta n phi.1)) hXnorm 2
    have hsquareY := pow_le_pow_left₀
      (norm_nonneg (gk16ScalarYModel38 F beta n phi.1)) hYnorm 2
    constructor
    · simpa only [halgebra] using hsquareX
    · simpa only [halgebra] using hsquareY
  have hmajor : Summable (fun n : ℤ => C*‖gk151BetaMass38 phi.1 n‖^2) :=
    hmassSum.mul_left C
  have hsumX : Summable (fun n : ℤ => ‖gk16ScalarXModel38 F beta n phi.1‖^2) :=
    hmajor.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => (hpoint n).1)
  have hsumY : Summable (fun n : ℤ => ‖gk16ScalarYModel38 F beta n phi.1‖^2) :=
    hmajor.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => (hpoint n).2)
  refine ⟨hxi,hexpBeta,hweighted,hmassSum,hmassBound,hpoint,hsumX,hsumY,?_,?_⟩
  · calc
      (∑' n : ℤ, ‖gk16ScalarXModel38 F beta n phi.1‖^2) ≤
          ∑' n : ℤ, C*‖gk151BetaMass38 phi.1 n‖^2 :=
        hsumX.tsum_le_tsum (fun n => (hpoint n).1) hmajor
      _ = C*(∑' n : ℤ, ‖gk151BetaMass38 phi.1 n‖^2) := tsum_mul_left
      _ ≤ C*M := mul_le_mul_of_nonneg_left hmassBound hC
      _ = 8*X^2*Real.exp (2*(K+b0))*M := rfl
  · calc
      (∑' n : ℤ, ‖gk16ScalarYModel38 F beta n phi.1‖^2) ≤
          ∑' n : ℤ, C*‖gk151BetaMass38 phi.1 n‖^2 :=
        hsumY.tsum_le_tsum (fun n => (hpoint n).2) hmajor
      _ = C*(∑' n : ℤ, ‖gk151BetaMass38 phi.1 n‖^2) := tsum_mul_left
      _ ≤ C*M := mul_le_mul_of_nonneg_left hmassBound hC
      _ = 8*X^2*Real.exp (2*(K+b0))*M := rfl

/-- OUTERL2-012-DOMAIN: union of common real-centered bounded charts
supplies the precise existing Hilbert-realization input at EVERY point of an
open complex neighborhood. No Hilbert or physical map is defined here. -/
theorem gk16_same_family_xy_local_l2_domain38
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
    : ∃ U : Set PotPair,
      IsOpen U ∧ range realSlice ⊆ U ∧ U ⊆ V ∩ xiCommonDomain38 ∧
      ∀ phi0 : PotPair, phi0 ∈ U →
        IsLocUnifL2Seq (fun phi n => gk16ScalarXModel38 F beta n phi) phi0 ∧
        IsLocUnifL2Seq (fun phi n => gk16ScalarYModel38 F beta n phi) phi0 := by
  classical
  let Good : PhysicalL2 → ℝ → ℝ → Prop := fun u delta C =>
    0 < delta ∧ ball (realSlice u) delta ⊆ V ∩ xiCommonDomain38 ∧
      ∀ phi ∈ ball (realSlice u) delta,
        Summable (fun n : ℤ => ‖gk16ScalarXModel38 F beta n phi‖^2) ∧
        (∑' n : ℤ, ‖gk16ScalarXModel38 F beta n phi‖^2) ≤ C ∧
        Summable (fun n : ℤ => ‖gk16ScalarYModel38 F beta n phi‖^2) ∧
        (∑' n : ℤ, ‖gk16ScalarYModel38 F beta n phi‖^2) ≤ C
  have hgood (u : PhysicalL2) : ∃ delta C : ℝ, Good u delta C := by
    obtain ⟨delta,b0,K,X,M,hdelta,_hb0,_hK,_hX,_hM,hsub,hbound⟩ :=
      gk16_same_family_xy_outer_l2_bound38 W hWopen hreal hWgk F
        hFanalytic hFn hFinv hperiod hFreal V hVopen hrealV hVW beta hbeta u
    refine ⟨delta,8*X^2*Real.exp (2*(K+b0))*M,hdelta,hsub,?_⟩
    intro phi hphi
    have hphiW : phi ∈ W := hVW (hsub hphi).1
    obtain ⟨_hxi,_hexp,_hweighted,_hmass,_hmassBound,_hpoint,hsX,hsY,hX,hY⟩ :=
      hbound ⟨phi,hphiW⟩ hphi
    exact ⟨hsX,hX,hsY,hY⟩
  let U : Set PotPair := {phi | ∃ u : PhysicalL2, ∃ delta C : ℝ,
    Good u delta C ∧ phi ∈ ball (realSlice u) delta}
  have hUopen : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro phi hphi
    obtain ⟨u,delta,C,hgood,hphiBall⟩ := hphi
    exact Filter.mem_of_superset (isOpen_ball.mem_nhds hphiBall)
      (fun psi hpsi => ⟨u,delta,C,hgood,hpsi⟩)
  have hrealU : range realSlice ⊆ U := by
    rintro phi ⟨u,rfl⟩
    obtain ⟨delta,C,hG⟩ := hgood u
    exact ⟨u,delta,C,hG,mem_ball_self hG.1⟩
  have hsub : U ⊆ V ∩ xiCommonDomain38 := by
    intro phi hphi
    obtain ⟨u,delta,C,hG,hphiBall⟩ := hphi
    exact hG.2.1 hphiBall
  refine ⟨U,hUopen,hrealU,hsub,?_⟩
  intro phi0 hphi0
  obtain ⟨u,delta,C,hG,hphiBall⟩ := hphi0
  constructor
  · refine ⟨ball (realSlice u) delta,isOpen_ball.mem_nhds hphiBall,C,?_⟩
    intro phi hphi
    exact ⟨(hG.2.2 phi hphi).1,(hG.2.2 phi hphi).2.1⟩
  · refine ⟨ball (realSlice u) delta,isOpen_ball.mem_nhds hphiBall,C,?_⟩
    intro phi hphi
    exact ⟨(hG.2.2 phi hphi).2.2.1,(hG.2.2 phi hphi).2.2.2⟩

end
end NlsGge.GK38
