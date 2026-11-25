import Armstrong.Work.RawEtaZetaEstimate
import Armstrong.Work.QuadraticCircleODE
import Armstrong.Work.RawBetaFixedAnalytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Speculative regular correction for the diagonal exponential

The own omitted quotient is q, with exact mean one and
`psi / canonRoot = I * q / stdRoot`.  We do not identify it with the printed
negative product named zeta in GK Section 16.  Subtracting 1 produces a genuine
zero-period numerator and hence an explicit analytic quadratic coefficient.

This is ordinary infrastructure for a sign-explicit alternative implementation
of GK 16.2.  It does not define eta or assert a Cartesian coordinate theorem.
Candidate predecessors are not independently accepted yet.
-/
set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- Exact vanishing period after removing the model own-gap numerator. -/
theorem gk16_own_correction_zero_period38
    (phi : PotPair) (hphi : phi ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 phi C R)
    (n : ℤ) (s : Lib.L2Seq)
    (hperiod : abelianPeriod38 n phi (p2FullNumerator38 n s) =
      2 * (Real.pi : ℂ)) :
    CircleIntegrable
      (fun z => (p2OmittedRatio38 n ((phi,s),z)-1) /
        stdRoot38 ((lamMinus phi n+lamPlus phi n)/2)
          ((lamPlus phi n-lamMinus phi n)^2) z) (C n) (R n) ∧
    circleIntegral
      (fun z => (p2OmittedRatio38 n ((phi,s),z)-1) /
        stdRoot38 ((lamMinus phi n+lamPlus phi n)/2)
          ((lamPlus phi n-lamMinus phi n)^2) z) (C n) (R n) = 0 := by
  have hr : 0 < R n := isolating_radius_pos38 hfam n
  have hcut : segment ℝ (lamMinus phi n) (lamPlus phi n) ⊆
      ball (C n) (R n) := by
    obtain ⟨c,N,hgeom,hspec⟩ := hfam
    exact (hspec.1 n).1
  have hf := (gk16_own_ratio_analytic38 n phi hphi C R hfam s).sub
    (analyticOnNhd_const (v := (1 : ℂ)))
  have hmean := gk16_own_ratio_cosine_average38 phi hphi C R hfam n s hperiod
  have hcorr := p2StdRoot_cosine_average38
    (lamMinus phi n) (lamPlus phi n) (C n) (R n) hr hcut
    (fun z => p2OmittedRatio38 n ((phi,s),z)-1) hf
  refine ⟨hcorr.1, ?_⟩
  rw [hcorr.2.2, intervalIntegral.integral_sub hmean.1 intervalIntegrable_const,
    hmean.2]
  have hconst : (∫ theta : ℝ in (0:ℝ)..2*Real.pi, (1 : ℂ)) =
      2 * (Real.pi : ℂ) := by
    simp only [intervalIntegral.integral_const, sub_zero, Complex.real_smul,
      mul_one, Complex.ofReal_mul] <;> norm_num
  rw [hconst, sub_self, mul_zero]

/-- Literal Cauchy formula for the normalized own correction.  All analytic
claims below prove integrability before invoking the coefficient theorem. -/
def gk16OwnCorrectionCoefficient38
    (phi : PotPair) (n : ℤ) (s : Lib.L2Seq) (c : ℂ) (r : ℝ) : ℂ → ℂ :=
  rawBetaStdCauchyCoefficient38 (lamMinus phi n) (lamPlus phi n) c r
    (fun z => p2OmittedRatio38 n ((phi,s),z)-1)

/-- The correction is analytic on the original filled disc and solves the
quadratic equation, including the repeated-endpoint case. -/
theorem gk16_own_correction_coefficient38
    (phi : PotPair) (hphi : phi ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 phi C R)
    (n : ℤ) (s : Lib.L2Seq)
    (hperiod : abelianPeriod38 n phi (p2FullNumerator38 n s) =
      2 * (Real.pi : ℂ)) :
    let T := gk16OwnCorrectionCoefficient38 phi n s (C n) (R n)
    AnalyticOnNhd ℂ T (ball (C n) (R n)) ∧
      ∀ z ∈ ball (C n) (R n),
        (z-lamMinus phi n)*(z-lamPlus phi n)*deriv T z +
          (z-(lamMinus phi n+lamPlus phi n)/2)*T z =
            p2OmittedRatio38 n ((phi,s),z)-1 := by
  have hr : 0 < R n := isolating_radius_pos38 hfam n
  have hcut : segment ℝ (lamMinus phi n) (lamPlus phi n) ⊆
      ball (C n) (R n) := by
    obtain ⟨c,N,hgeom,hspec⟩ := hfam
    exact (hspec.1 n).1
  have hf := (gk16_own_ratio_analytic38 n phi hphi C R hfam s).sub
    (analyticOnNhd_const (v := (1 : ℂ)))
  have hp := gk16_own_correction_zero_period38 phi hphi C R hfam n s hperiod
  exact rawBetaQuadraticODEOfZeroStdRootPeriodExplicit38
    (lamMinus phi n) (lamPlus phi n) (C n) (R n) hr hcut
    (fun z => p2OmittedRatio38 n ((phi,s),z)-1) hf hp.2

/-- At a repeated endpoint, normalization forces q=1 exactly. -/
theorem gk16_own_correction_collapsed_value38
    (phi : PotPair) (hphi : phi ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 phi C R)
    (n : ℤ) (s : Lib.L2Seq)
    (hperiod : abelianPeriod38 n phi (p2FullNumerator38 n s) =
      2 * (Real.pi : ℂ))
    (hgap : lamPlus phi n = lamMinus phi n) :
    p2OmittedRatio38 n ((phi,s),lamMinus phi n) = 1 := by
  have ha : lamMinus phi n ∈ ball (C n) (R n) := by
    obtain ⟨c,N,hgeom,hspec⟩ := hfam
    exact (hspec.1 n).1 (left_mem_segment ℝ _ _)
  have hode := (gk16_own_correction_coefficient38 phi hphi C R hfam n s
    hperiod).2 (lamMinus phi n) ha
  have hmid : (lamMinus phi n+lamPlus phi n)/2 = lamMinus phi n := by
    rw [hgap]
    ring
  simp only [hmid, sub_self, zero_mul, zero_add] at hode
  exact sub_eq_zero.mp hode.symm

/-- A source-independent local algebraic calculation for the two sheet signs.
The square root and coefficient are genuine differentiable functions; no
exponential, eta, or Cartesian target is assumed. -/
theorem gk16_correction_exponential_hasDerivAt38
    (a b z eps q : ℂ) (w T : ℂ → ℂ) (wd Td : ℂ)
    (heps : eps^2 = 1) (hwn : w z ≠ 0)
    (hw : HasDerivAt w wd z) (hT : HasDerivAt T Td z)
    (hroot : (w z)^2 = (z-a)*(z-b))
    (hrootder : w z*wd = z-(a+b)/2)
    (hode : (z-a)*(z-b)*Td + (z-(a+b)/2)*T z = q-1) :
    HasDerivAt
      (fun x => (2*((a+b)/2-x)-2*eps*w x) *
        Complex.exp (eps*w x*T x))
      ((eps*q/w z) * ((2*((a+b)/2-z)-2*eps*w z) *
        Complex.exp (eps*w z*T z))) z := by
  have hwd : wd = (z-(a+b)/2)/w z := by
    apply (eq_div_iff hwn).2
    simpa only [mul_comm] using hrootder
  have hc : wd*T z+w z*Td = (q-1)/w z := by
    apply (eq_div_iff hwn).2
    calc
      (wd*T z+w z*Td)*w z =
          (w z*wd)*T z+(w z)^2*Td := by ring
      _ = q-1 := by rw [hrootder, hroot]; linear_combination hode
  have hp : -2-2*eps*wd =
      (eps/w z)*(2*((a+b)/2-z)-2*eps*w z) := by
    rw [hwd]
    field_simp [hwn]
    linear_combination 2 * w z * heps
  have hdP : HasDerivAt
      (fun x => 2*((a+b)/2-x)-2*eps*w x) (-2-2*eps*wd) z := by
    convert ((((hasDerivAt_id z).const_sub ((a+b)/2)).const_mul 2).sub
      (hw.const_mul (2*eps))) using 1
    · funext x
      simp only [Pi.sub_apply,id_eq]
    · ring
  have hdF : HasDerivAt (fun x : ℂ => eps*w x*T x)
      (eps*(wd*T z+w z*Td)) z := by
    simpa only [Pi.mul_apply,mul_assoc] using (hw.mul hT).const_mul eps
  have hdE := hdF.cexp
  apply (hdP.mul hdE).congr_deriv
  rw [hp, hc]
  field_simp [hwn]
  ring

/-- The sheet-exponential model has the required initial gap value at either
sign, without division by the square root at the endpoint. -/
theorem gk16_correction_exponential_left_endpoint38
    (a b eps : ℂ) (w T : ℂ → ℂ) (hwa : w a = 0) :
    (2*((a+b)/2-a)-2*eps*w a) *
      Complex.exp (eps*w a*T a) = b-a := by
  rw [hwa]
  simp only [mul_zero, zero_mul, Complex.exp_zero, sub_zero, mul_one]
  ring

/-- Parameter analyticity of a standard-root Cauchy coefficient uses only
symmetric spectral data.  No analytic labelling of the two endpoints is assumed. -/
theorem gk16_standard_correction_joint_analytic38
    (V : Set PotPair) (hV : IsOpen V) (hVg : V ⊆ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : ∀ phi ∈ V, IsolatingFamily38 phi C R)
    (n : ℤ) (Q : PotPair × ℂ → ℂ)
    (hQ : AnalyticOnNhd ℂ Q (V ×ˢ sphere (C n) (R n))) :
    AnalyticOnNhd ℂ
      (fun p : PotPair × ℂ => rawBetaStdCauchyCoefficient38
        (lamMinus p.1 n) (lamPlus p.1 n) (C n) (R n)
        (fun z => Q (p.1,z)) p.2)
      (V ×ˢ ball (C n) (R n)) := by
  intro p hp
  have hr : 0 < R n := isolating_radius_pos38 (hfamily p.1 hp.1) n
  let U : Set (PotPair × ℂ) := V ×ˢ ball (C n) (R n)
  have hU : IsOpen U := hV.prod isOpen_ball
  let A : (PotPair × ℂ) → ℂ → ℂ := fun x w =>
    ((w-C n)*Complex.I)*Q (x.1,w) /
      stdRoot38 (tauN x.1 n) (gamma2 x.1 n) w
  let B : (PotPair × ℂ) → ℂ → ℂ := fun x w =>
    ((w-C n)*Complex.I) /
      (stdRoot38 (tauN x.1 n) (gamma2 x.1 n) w*(w-x.2))
  have hJ : ∀ q : (PotPair × ℂ) × ℂ,
      AnalyticAt ℂ (fun y : (PotPair × ℂ) × ℂ => (y.1.1,y.2)) q := by
    intro q
    have hphi : AnalyticAt ℂ (fun y : (PotPair × ℂ) × ℂ => y.1.1) q :=
      AnalyticAt.comp (g := fun x : PotPair × ℂ => x.1)
        (f := fun y : (PotPair × ℂ) × ℂ => y.1)
        analyticAt_fst analyticAt_fst
    exact hphi.prod analyticAt_snd
  have hS := rawBetaFixedStandardRoot_analytic38 V hVg C R hfamily n
  have hSn : ∀ q ∈ U ×ˢ sphere (C n) (R n),
      stdRoot38 (tauN q.1.1 n) (gamma2 q.1.1 n) q.2 ≠ 0 := by
    intro q hq
    exact ((rawBetaFixedBoundaryRoot38 q.1.1 (hVg hq.1.1)
      C R (hfamily q.1.1 hq.1.1) n).2.2 q.2 hq.2).1
  have hSa : ∀ q ∈ U ×ˢ sphere (C n) (R n),
      AnalyticAt ℂ
        (fun y : (PotPair × ℂ) × ℂ =>
          stdRoot38 (tauN y.1.1 n) (gamma2 y.1.1 n) y.2) q := by
    intro q hq
    exact AnalyticAt.comp
      (g := fun x : PotPair × ℂ => stdRoot38 (tauN x.1 n) (gamma2 x.1 n) x.2)
      (f := fun y : (PotPair × ℂ) × ℂ => (y.1.1,y.2)) (x := q)
      (hS (q.1.1,q.2) ⟨hq.1.1,hq.2⟩) (hJ q)
  have hfactor : ∀ q : (PotPair × ℂ) × ℂ,
      AnalyticAt ℂ (fun y : (PotPair × ℂ) × ℂ => (y.2-C n)*Complex.I) q :=
    fun _ => (analyticAt_snd.sub analyticAt_const).mul analyticAt_const
  have hA : AnalyticOnNhd ℂ (Function.uncurry A)
      (U ×ˢ sphere (C n) (R n)) := by
    intro q hq
    have hQa : AnalyticAt ℂ (fun y : (PotPair × ℂ) × ℂ => Q (y.1.1,y.2)) q :=
      AnalyticAt.comp (g := Q)
        (f := fun y : (PotPair × ℂ) × ℂ => (y.1.1,y.2)) (x := q)
        (hQ (q.1.1,q.2) ⟨hq.1.1,hq.2⟩) (hJ q)
    exact ((hfactor q).mul hQa).div (hSa q hq) (hSn q hq)
  have hB : AnalyticOnNhd ℂ (Function.uncurry B)
      (U ×ˢ sphere (C n) (R n)) := by
    intro q hq
    have hden : q.2-q.1.2 ≠ 0 := by
      apply sub_ne_zero.mpr
      intro he
      have hs := mem_sphere.mp hq.2
      rw [he] at hs
      exact (not_lt.mpr hs.ge) (mem_ball.mp hq.1.2)
    have hz : AnalyticAt ℂ (fun y : (PotPair × ℂ) × ℂ => y.1.2) q :=
      AnalyticAt.comp (g := fun x : PotPair × ℂ => x.2)
        (f := fun y : (PotPair × ℂ) × ℂ => y.1)
        analyticAt_snd analyticAt_fst
    exact (hfactor q).div ((hSa q hq).mul (analyticAt_snd.sub hz))
      (mul_ne_zero (hSn q hq) hden)
  have hNested := Lib.parametricNestedCircle_analytic38
    hU hr hA hB (0:ℝ) (0:ℝ) (2*Real.pi)
  let E : PotPair × ℂ → ℂ := fun x =>
    (2*(Real.pi:ℂ)*Complex.I)⁻¹ *
      (∫ theta in (0:ℝ)..2*Real.pi,
        (∫ t in (0:ℝ)..theta, A x (circleMap (C n) (R n) t)) *
          B x (circleMap (C n) (R n) theta))
  have hE : AnalyticOnNhd ℂ E U := analyticOnNhd_const.mul hNested
  have hgammaD (t : ℝ) : deriv (circleMap (C n) (R n)) t =
      (circleMap (C n) (R n) t-C n)*Complex.I := by
    rw [deriv_circleMap,circleMap_sub_center]
  have hEqual : EqOn E
      (fun x : PotPair × ℂ => rawBetaStdCauchyCoefficient38
        (lamMinus x.1 n) (lamPlus x.1 n) (C n) (R n)
        (fun z => Q (x.1,z)) x.2) U := by
    intro x hx
    have htau : tauN x.1 n = (lamMinus x.1 n+lamPlus x.1 n)/2 := by
      rw [tauN_value38 x.1 (hVg hx.1) n]
      ring
    have hgamma := gamma2_value38 x.1 (hVg hx.1) n
    have hInner :
        (fun t : ℝ => A x (circleMap (C n) (R n) t)) =
        (fun t : ℝ => deriv (circleMap (C n) (R n)) t *
          (Q (x.1,circleMap (C n) (R n) t) /
            stdRoot38 (tauN x.1 n) (gamma2 x.1 n)
              (circleMap (C n) (R n) t))) := by
      funext t
      dsimp only [A]
      rw [hgammaD t]
      ring
    have hOuter :
        (fun theta : ℝ =>
          (∫ t in (0:ℝ)..theta, A x (circleMap (C n) (R n) t)) *
            B x (circleMap (C n) (R n) theta)) =
        (fun theta : ℝ =>
          ((∫ t in (0:ℝ)..theta, deriv (circleMap (C n) (R n)) t *
            (Q (x.1,circleMap (C n) (R n) t) /
              stdRoot38 (tauN x.1 n) (gamma2 x.1 n)
                (circleMap (C n) (R n) t))) /
            stdRoot38 (tauN x.1 n) (gamma2 x.1 n)
              (circleMap (C n) (R n) theta)) *
            deriv (circleMap (C n) (R n)) theta /
              (circleMap (C n) (R n) theta-x.2)) := by
      funext theta
      have hSnx := ((rawBetaFixedBoundaryRoot38 x.1 (hVg hx.1)
        C R (hfamily x.1 hx.1) n).2.2
          (circleMap (C n) (R n) theta) (circleMap_mem_sphere (C n) hr.le theta)).1
      have hden : circleMap (C n) (R n) theta-x.2 ≠ 0 :=
        sub_ne_zero.mpr (circleMap_ne_mem_ball hx.2 theta)
      dsimp only [B]
      rw [hInner,hgammaD theta]
      field_simp [hSnx,hden] <;> ring
    dsimp only [E,rawBetaStdCauchyCoefficient38,rawBetaBoundaryCauchy38]
    rw [← htau,← hgamma,← hOuter]
  exact (AnalyticOnNhd.congr hU hE hEqual) p hp

/-- The actual full-input family gives a jointly analytic correction on the
same fixed disc, across potential values where the own gap collapses. -/
theorem gk16_own_correction_joint_analytic38
    (V : Set PotPair) (hV : IsOpen V) (hVg : V ⊆ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : ∀ phi ∈ V, IsolatingFamily38 phi C R)
    (n : ℤ) (S : PotPair → Lib.L2Seq) (hS : AnalyticOnNhd ℂ S V) :
    AnalyticOnNhd ℂ
      (fun p : PotPair × ℂ =>
        gk16OwnCorrectionCoefficient38 p.1 n (S p.1) (C n) (R n) p.2)
      (V ×ˢ ball (C n) (R n)) := by
  have hQ : AnalyticOnNhd ℂ
      (fun p : PotPair × ℂ => p2OmittedRatio38 n ((p.1,S p.1),p.2)-1)
      (V ×ˢ sphere (C n) (R n)) := by
    intro p hp
    have hinput : AnalyticAt ℂ
        (fun q : PotPair × ℂ => ((q.1,S q.1),q.2)) p :=
      (analyticAt_fst.prod ((hS p.1 hp.1).comp analyticAt_fst)).prod analyticAt_snd
    have hdom := a5OwnClosedBall_omittedDomain38 p.1 (hVg hp.1) C R
      (hfamily p.1 hp.1) n p.2 (sphere_subset_closedBall hp.2)
    have hratio : AnalyticAt ℂ
        (fun q : PotPair × ℂ => p2OmittedRatio38 n ((q.1,S q.1),q.2)) p :=
      AnalyticAt.comp (g := p2OmittedRatio38 n)
        (f := fun q : PotPair × ℂ => ((q.1,S q.1),q.2)) (x := p)
        (p2OmittedRatio_analytic38 n ((p.1,S p.1),p.2) hdom) hinput
    exact hratio.sub analyticAt_const
  exact gk16_standard_correction_joint_analytic38 V hV hVg C R hfamily n
    (fun p => p2OmittedRatio38 n ((p.1,S p.1),p.2)-1) hQ

/-- Actual same-W/same-F production of the jointly analytic correction.  One
neighborhood is chosen before all signed indices, and the original full-input
branch supplies both the numerator identity and the exact own period. -/
theorem gk16_same_family_correction38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0)
    (hFinv : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (phi,y))
        (F n phi)).IsInvertible)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t)
    (u : PhysicalL2) :
    ∃ delta : ℝ, 0 < delta ∧ ball (realSlice u) delta ⊆ W ∧
      ∀ n : ℤ, ∃ S : PotPair → Lib.L2Seq,
        AnalyticOnNhd ℂ S (ball (realSlice u) delta) ∧
        (∀ phi ∈ ball (realSlice u) delta,
          F n phi = p2Restrict38 n (S phi) ∧
          p6PsiNumerator38 n (F n) phi = p2FullNumerator38 n (S phi) ∧
          abelianPeriod38 n phi (p2FullNumerator38 n (S phi)) =
            2 * (Real.pi : ℂ)) ∧
        AnalyticOnNhd ℂ
          (fun p : PotPair × ℂ => gk16OwnCorrectionCoefficient38
            p.1 n (S p.1) (discC (realSlice u) n) (discR (realSlice u) n) p.2)
          (ball (realSlice u) delta ×ˢ
            ball (discC (realSlice u) n) (discR (realSlice u) n)) ∧
        ∀ phi ∈ ball (realSlice u) delta,
          let T := gk16OwnCorrectionCoefficient38 phi n (S phi)
            (discC (realSlice u) n) (discR (realSlice u) n)
          ∀ z ∈ ball (discC (realSlice u) n) (discR (realSlice u) n),
            (z-lamMinus phi n)*(z-lamPlus phi n)*deriv T z +
              (z-(lamMinus phi n+lamPlus phi n)/2)*T z =
                p2OmittedRatio38 n ((phi,S phi),z)-1 := by
  have huW : realSlice u ∈ W := hreal (mem_range_self u)
  have huGK : realSlice u ∈ gkW := hWgk huW
  let C : ℤ → ℂ := discC (realSlice u)
  let R : ℤ → ℝ := discR (realSlice u)
  have hfam0 : IsolatingFamily38 (realSlice u) C R :=
    isolating_family38 (realSlice u) huGK
  obtain ⟨rho,hrho,hrhoW,hbranches⟩ :=
    gk16_same_family_own_quotient38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal u
  obtain ⟨r,hr,c,N,hgeom,hpersist⟩ :=
    fixed_family_persistence38 (realSlice u) C R hfam0
  let delta : ℝ := min rho r
  have hdelta : 0 < delta := lt_min hrho hr
  have hsubrho : ball (realSlice u) delta ⊆ ball (realSlice u) rho :=
    ball_subset_ball (min_le_left _ _)
  have hsubr : ball (realSlice u) delta ⊆ ball (realSlice u) r :=
    ball_subset_ball (min_le_right _ _)
  have hsubW : ball (realSlice u) delta ⊆ W := hsubrho.trans hrhoW
  have hfamily : ∀ phi ∈ ball (realSlice u) delta,
      IsolatingFamily38 phi C R :=
    fun phi hphi => ⟨c,N,hgeom,hpersist phi (hsubr hphi)⟩
  refine ⟨delta,hdelta,hsubW,?_⟩
  intro n
  obtain ⟨S,hS,hSspec⟩ := hbranches n
  have hSsmall := hS.mono hsubrho
  refine ⟨S,hSsmall,?_,?_,?_⟩
  · intro phi hphi
    obtain ⟨hrestrict,hnum,hroots,hqan,hqnz,hown,heq⟩ :=
      hSspec phi (hsubrho hphi)
    exact ⟨hrestrict,hnum,hown⟩
  · exact gk16_own_correction_joint_analytic38
      (ball (realSlice u) delta) isOpen_ball (hsubW.trans hWgk)
      C R hfamily n S hSsmall
  · intro phi hphi
    obtain ⟨hrestrict,hnum,hroots,hqan,hqnz,hown,heq⟩ :=
      hSspec phi (hsubrho hphi)
    exact (gk16_own_correction_coefficient38 phi (hWgk (hsubW hphi))
      C R (hfamily phi hphi) n (S phi) hown).2

end
end NlsGge.GK38
