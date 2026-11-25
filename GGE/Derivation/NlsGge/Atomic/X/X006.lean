import Mathlib
import Armstrong.Work.ActualPhysicalSmallBallFiniteGap
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38

/- X-006 PRODUCTION01 (proof development, AUTHOR; independent review: proof development).  Target NlsGge/Atomic/X/X006.lean.
   Structure PhysicalLocalFamily verbatim from DEFINITIONS/COMMON.lean.md and the head `actualSmallBall_finiteGap_reuse` verbatim from STATEMENTS/X.md X-006:
   checked token-identical (whitespace-normalized) against defs3, followup1 and followup2 (commit 1b36c77b); Pro did not change X-006.
   Constructor: repackaging of NlsGge.GK38.a7_actual_physical_small_ball_finite_gap_producer065 from Armstrong.Work.ActualPhysicalSmallBallFiniteGap.
   OWNER DECISION 2026-10-30 (option 1; root/AUDIT_DEFERRED_NOTES01.md, "OWNER DECISION: X-006 Armstrong anchors"): production may import the Armstrong anchors in
   X-006's producer closure (root/X006_ARMSTRONG_BASE_MODULES01.txt, 92 lines, incl. 23 Armstrong.Frozen modules reached through Armstrong.Providers) for X-006 and its
   consumers only; this is not a general waiver and the anchors are not accepted packets.  The record fields are the producer's witnesses in the same order; the small
   ball is the producer's own delta in the physical L2 topology (no Sobolev restriction, no global inverse).  The structure is built positionally. -/
set_option autoImplicit false

open Set NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
namespace NlsGge.Atomic.ExistingPhysicalFamily
noncomputable section

structure PhysicalLocalFamily where
  W : Set PotPair
  W_open : IsOpen W
  W_real : range realSlice ⊆ W
  W_gk : W ⊆ gkW
  F : (n : ℤ) → PotPair → P2Space38 n
  F_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W
  F_zero : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
    p2Fn38 n (phi, F n phi) = 0
  F_inverse : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
    (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (phi, y))
      (F n phi)).IsInvertible
  F_period : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
    abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
      if m = n then 2 * (Real.pi : ℂ) else 0
  F_real : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
    t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
      F n (realSlice u) = p3RealInclude38 n t
  V : Set PotPair
  beta : ℤ → PotPair → ℂ
  V_open : IsOpen V
  V_real : range realSlice ⊆ V
  V_W : V ⊆ W
  V_xi : V ⊆ xiCommonDomain38
  beta_spec : ∀ n : ℤ, ∀ phi : {chi : PotPair // chi ∈ W}, phi.1 ∈ V →
    Summable (fun m : P2Index38 n =>
      ‖gkSourceBeta38 W W_open W_real W_gk F
        F_analytic F_zero F_period n m.1 m.2 phi‖) ∧
    beta n phi.1 = ∑' m : P2Index38 n,
      gkSourceBeta38 W W_open W_real W_gk F
        F_analytic F_zero F_period n m.1 m.2 phi
  XY_analytic : ∀ n : ℤ,
    AnalyticOnNhd ℂ (gk16ScalarXModel38 F beta n) V ∧
    AnalyticOnNhd ℂ (gk16ScalarYModel38 F beta n) V
  Phi : PhysicalL2 → Lib.L2Z
  Phi_continuous : Continuous Phi
  Phi_formula : ∀ (u : PhysicalL2) (n : ℤ),
    Phi u n = (xiN38 n (realSlice u) / 2) *
      (gk16ActualScalarZMinus38 F n (realSlice u) *
        Complex.exp (-Complex.I * beta n (realSlice u)))
  Phi_action : ∀ (u : PhysicalL2) (n : ℤ),
    ‖Phi u n‖ ^ 2 = actualGapActionAllE02_38 u n
  Phi_mass : ∀ u : PhysicalL2,
    HasSum (fun n : ℤ => actualGapActionAllE02_38 u n) (‖u‖ ^ 2) ∧
      ‖Phi u‖ ^ 2 = ‖u‖ ^ 2
  Phi_analytic : ∀ u : PhysicalL2, AnalyticAt ℝ Phi u
  Phi_derivative_zero : HasFDerivAt Phi
    (reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)
    (0 : PhysicalL2)
  e : OpenPartialHomeomorph PhysicalL2 Lib.L2Z
  e_source_zero : (0 : PhysicalL2) ∈ e.source
  e_target_zero : (0 : Lib.L2Z) ∈ e.target
  e_forward : (⇑e : PhysicalL2 → Lib.L2Z) = Phi
  e_zero : e (0 : PhysicalL2) = 0
  e_inverse_analytic : AnalyticAt ℝ e.symm (0 : Lib.L2Z)
  delta : ℝ
  delta_pos : 0 < delta
  source_ball : Metric.ball (0 : PhysicalL2) delta ⊆ e.source
  target_ball : Metric.ball (0 : Lib.L2Z) delta ⊆ e.target
  chart_ball : (e.source ∩ Phi ⁻¹' Metric.ball (0 : Lib.L2Z) delta) =
    Metric.ball (0 : PhysicalL2) delta
  finite_gap_closure : Metric.ball (0 : PhysicalL2) delta ⊆
    closure (Metric.ball (0 : PhysicalL2) delta ∩
      {u : PhysicalL2 | {n : ℤ | actualGapLowerAllE02_38 u n <
        actualGapUpperAllE02_38 u n}.Finite})

/- Enriched existence theorem for the single X-006 selection (Pro round 8, section 27, G2-074 / G4-039).
    Retains the p6 quadratic-mass witness of the SAME W,F (the a7 producer discards it as _hmass) and
    the earned local-L2 scalar domain U (gk16_same_family_xy_local_l2_domain38). Proof: the a7 producer
    body with these two retentions; the chart/Phi construction is run on the scalar domain V, which the
    record never uses except through U ⊆ V (all record fields are restricted coherently).
    Decision 17 (owner, 2026-11-01; root/AUDIT_DEFERRED_NOTES01.md): third conjunct retains that every point of
    D.V lies in a ball around a real potential contained in D.V (U is built inline as a union of such balls). -/
open Topology in
theorem physicalLocalFamily_with_retained_bounds :
    ∃ D : PhysicalLocalFamily,
      (∀ φ₀ : PotPair, φ₀ ∈ D.W →
        ∃ V : Set PotPair,
          IsOpen V ∧ φ₀ ∈ V ∧ V ⊆ D.W ∧
          ∃ B : ℝ, 0 < B ∧
            ∀ φ : PotPair, φ ∈ V →
              ∀ n : ℤ, ∃ A : P2Space38 n,
                (∀ m : P2Index38 n,
                  countingCenter38 m.1 + D.F n φ m =
                    tauN φ m.1 + gamma2 φ m.1 * A m) ∧
                Summable (fun m : P2Index38 n => ‖A m‖^2) ∧
                (∑' m : P2Index38 n, ‖A m‖^2) ≤ B) ∧
      (∀ φ₀ : PotPair, φ₀ ∈ D.V →
        ∃ V : Set PotPair,
          V ∈ 𝓝 φ₀ ∧ V ⊆ D.V ∧
          ∃ C : ℝ, 0 < C ∧
            ∀ φ : PotPair, φ ∈ V →
              Summable (fun n : ℤ =>
                ‖gk16ScalarXModel38 D.F D.beta n φ‖^2) ∧
              (∑' n : ℤ,
                ‖gk16ScalarXModel38 D.F D.beta n φ‖^2) ≤ C ∧
              Summable (fun n : ℤ =>
                ‖gk16ScalarYModel38 D.F D.beta n φ‖^2) ∧
              (∑' n : ℤ,
                ‖gk16ScalarYModel38 D.F D.beta n φ‖^2) ≤ C) ∧
      (∀ φ ∈ D.V, ∃ u : PhysicalL2, ∃ r : ℝ, 0 < r ∧
          φ ∈ Metric.ball (realSlice u) r ∧ Metric.ball (realSlice u) r ⊆ D.V) := by
  obtain ⟨W,hWopen,hreal,hWgk,F,hFanalytic,_hjoint,_hroots,
    hspec,hrealspec,_hfree,hmass⟩ := p6Actual_psi_theorem141_same_family38
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
  -- Decision 17 (owner, 2026-11-01): inline copy of the proof body of
  -- gk16_same_family_xy_local_l2_domain38 (Armstrong/Work/ActualCartesianXYModels.lean:465-540),
  -- additionally retaining that U is a union of balls centred on real potentials.
  obtain ⟨U,hUopen,hrealU,hUsub,hUloc,hUball⟩ :
      ∃ U : Set PotPair,
        IsOpen U ∧ range realSlice ⊆ U ∧ U ⊆ V ∩ xiCommonDomain38 ∧
        (∀ phi0 : PotPair, phi0 ∈ U →
          IsLocUnifL2Seq (fun phi n => gk16ScalarXModel38 F beta n phi) phi0 ∧
          IsLocUnifL2Seq (fun phi n => gk16ScalarYModel38 F beta n phi) phi0) ∧
        (∀ φ ∈ U, ∃ u : PhysicalL2, ∃ r : ℝ, 0 < r ∧
          φ ∈ Metric.ball (realSlice u) r ∧ Metric.ball (realSlice u) r ⊆ U) := by
    let Good : PhysicalL2 → ℝ → ℝ → Prop := fun u delta C =>
      0 < delta ∧ Metric.ball (realSlice u) delta ⊆ V ∩ xiCommonDomain38 ∧
        ∀ phi ∈ Metric.ball (realSlice u) delta,
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
    let U0 : Set PotPair := {phi | ∃ u : PhysicalL2, ∃ delta C : ℝ,
      Good u delta C ∧ phi ∈ Metric.ball (realSlice u) delta}
    have hU0open : IsOpen U0 := by
      apply isOpen_iff_mem_nhds.mpr
      intro phi hphi
      obtain ⟨u,delta,C,hgood,hphiBall⟩ := hphi
      exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hphiBall)
        (fun psi hpsi => ⟨u,delta,C,hgood,hpsi⟩)
    have hrealU0 : range realSlice ⊆ U0 := by
      rintro phi ⟨u,rfl⟩
      obtain ⟨delta,C,hG⟩ := hgood u
      exact ⟨u,delta,C,hG,Metric.mem_ball_self hG.1⟩
    have hsub0 : U0 ⊆ V ∩ xiCommonDomain38 := by
      intro phi hphi
      obtain ⟨u,delta,C,hG,hphiBall⟩ := hphi
      exact hG.2.1 hphiBall
    refine ⟨U0,hU0open,hrealU0,hsub0,?_,?_⟩
    · intro phi0 hphi0
      obtain ⟨u,delta,C,hG,hphiBall⟩ := hphi0
      constructor
      · refine ⟨Metric.ball (realSlice u) delta,Metric.isOpen_ball.mem_nhds hphiBall,C,?_⟩
        intro phi hphi
        exact ⟨(hG.2.2 phi hphi).1,(hG.2.2 phi hphi).2.1⟩
      · refine ⟨Metric.ball (realSlice u) delta,Metric.isOpen_ball.mem_nhds hphiBall,C,?_⟩
        intro phi hphi
        exact ⟨(hG.2.2 phi hphi).2.2.1,(hG.2.2 phi hphi).2.2.2⟩
    · intro φ hφ
      obtain ⟨u,delta,C,hG,hφBall⟩ := hφ
      exact ⟨u,delta,hG.1,hφBall,fun psi hpsi => ⟨u,delta,C,hG,hpsi⟩⟩
  have hUV : U ⊆ V := fun x hx => (hUsub hx).1
  have hUxi : U ⊆ xiCommonDomain38 := fun x hx => (hUsub hx).2
  have hUW : U ⊆ W := fun x hx => hVW (hUV hx)
  have hXYU : ∀ n : ℤ,
      AnalyticOnNhd ℂ (gk16ScalarXModel38 F beta n) U ∧
      AnalyticOnNhd ℂ (gk16ScalarYModel38 F beta n) U :=
    fun n => ⟨(hXY n).1.mono hUV, (hXY n).2.mono hUV⟩
  have hbetaU : ∀ n : ℤ, ∀ phi : {chi : PotPair // chi ∈ W}, phi.1 ∈ U →
      Summable (fun m : P2Index38 n =>
        ‖gkSourceBeta38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m.1 m.2 phi‖) ∧
      beta n phi.1 = (∑' m : P2Index38 n,
        gkSourceBeta38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m.1 m.2 phi) :=
    fun n phi hphi => hbeta n phi (hUV hphi)
  have hclause1 : ∀ φ₀ : PotPair, φ₀ ∈ W →
      ∃ V' : Set PotPair, IsOpen V' ∧ φ₀ ∈ V' ∧ V' ⊆ W ∧
        ∃ B : ℝ, 0 < B ∧ ∀ φ : PotPair, φ ∈ V' → ∀ n : ℤ, ∃ A : P2Space38 n,
          (∀ m : P2Index38 n,
            countingCenter38 m.1 + F n φ m = tauN φ m.1 + gamma2 φ m.1 * A m) ∧
          Summable (fun m : P2Index38 n => ‖A m‖^2) ∧
          (∑' m : P2Index38 n, ‖A m‖^2) ≤ B := by
    intro φ₀ hφ₀
    obtain ⟨V', B, hV'o, hφV', hV'W, hB, hA⟩ := hmass φ₀ hφ₀
    refine ⟨V', hV'o, hφV', hV'W, B, hB, fun φ hφ n => ?_⟩
    obtain ⟨A, _, hs, hle, hfac⟩ := hA n φ hφ
    exact ⟨A, hfac, hs, hle⟩
  have hclause2 : ∀ φ₀ : PotPair, φ₀ ∈ U →
      ∃ V' : Set PotPair, V' ∈ 𝓝 φ₀ ∧ V' ⊆ U ∧
        ∃ C : ℝ, 0 < C ∧ ∀ φ : PotPair, φ ∈ V' →
          Summable (fun n : ℤ => ‖gk16ScalarXModel38 F beta n φ‖^2) ∧
          (∑' n : ℤ, ‖gk16ScalarXModel38 F beta n φ‖^2) ≤ C ∧
          Summable (fun n : ℤ => ‖gk16ScalarYModel38 F beta n φ‖^2) ∧
          (∑' n : ℤ, ‖gk16ScalarYModel38 F beta n φ‖^2) ≤ C := by
    intro φ₀ hφ₀
    have hL := hUloc φ₀ hφ₀
    unfold IsLocUnifL2Seq at hL
    obtain ⟨⟨N1, hN1, c1, hc1⟩, ⟨N2, hN2, c2, hc2⟩⟩ := hL
    have hmem : N1 ∩ N2 ∩ U ∈ 𝓝 φ₀ :=
      Filter.inter_mem (Filter.inter_mem hN1 hN2) (hUopen.mem_nhds hφ₀)
    refine ⟨N1 ∩ N2 ∩ U, hmem, fun x hx => hx.2, |c1| + |c2| + 1, by positivity,
      fun φ hφ => ?_⟩
    obtain ⟨⟨h1, h2⟩, _⟩ := hφ
    obtain ⟨sX, bX⟩ := hc1 φ h1
    obtain ⟨sY, bY⟩ := hc2 φ h2
    have hc1C : c1 ≤ |c1| + |c2| + 1 := by linarith [le_abs_self c1, abs_nonneg c2]
    have hc2C : c2 ≤ |c1| + |c2| + 1 := by linarith [le_abs_self c2, abs_nonneg c1]
    exact ⟨sX, le_trans bX hc1C, sY, le_trans bY hc2C⟩
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
  obtain ⟨he0s,he0t,hefw,hez,heinv,dlt,hdlt,hsrc,htgt,hchart',hclos⟩ := hchartExtended
  exact ⟨PhysicalLocalFamily.mk W hWopen hreal hWgk F hFanalytic hFn hFinv hperiod hFreal
    U beta hUopen hrealU hUW hUxi hbetaU hXYU Phi hPhi hcoords hAction hMass hRealAnalytic
    hD0.1 e he0s he0t hefw hez heinv dlt hdlt hsrc htgt hchart' hclos,
    hclause1, hclause2, hUball⟩

theorem physicalLocalFamily_nonempty : Nonempty PhysicalLocalFamily :=
  ⟨Classical.choose physicalLocalFamily_with_retained_bounds⟩

-- The single public selection (Pro round 8, section 27). Its value is the choice of the enriched theorem.
noncomputable def actualPhysicalLocalFamily : PhysicalLocalFamily :=
  Classical.choose physicalLocalFamily_with_retained_bounds

theorem actualPhysicalLocalFamily_quadratic_mass
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ actualPhysicalLocalFamily.W) :
    ∃ V : Set PotPair,
      IsOpen V ∧ φ₀ ∈ V ∧ V ⊆ actualPhysicalLocalFamily.W ∧
      ∃ B : ℝ, 0 < B ∧
        ∀ φ : PotPair, φ ∈ V →
          ∀ n : ℤ, ∃ A : P2Space38 n,
            (∀ m : P2Index38 n,
              countingCenter38 m.1 +
                  actualPhysicalLocalFamily.F n φ m =
                tauN φ m.1 + gamma2 φ m.1 * A m) ∧
            Summable (fun m : P2Index38 n => ‖A m‖^2) ∧
            (∑' m : P2Index38 n, ‖A m‖^2) ≤ B :=
  (Classical.choose_spec physicalLocalFamily_with_retained_bounds).1 φ₀ hφ₀

theorem actualSmallBall_finiteGap_reuse :
    let D := actualPhysicalLocalFamily
    0 < D.delta ∧
    (⇑D.e : PhysicalL2 → Lib.L2Z) = D.Phi ∧
    (∀ (u : PhysicalL2) (n : ℤ),
      ‖D.Phi u n‖ ^ 2 = actualGapActionAllE02_38 u n) ∧
    Metric.ball (0 : PhysicalL2) D.delta ⊆ D.e.source ∧
    Metric.ball (0 : Lib.L2Z) D.delta ⊆ D.e.target ∧
    (D.e.source ∩ D.Phi ⁻¹' Metric.ball (0 : Lib.L2Z) D.delta) =
      Metric.ball (0 : PhysicalL2) D.delta ∧
    Metric.ball (0 : PhysicalL2) D.delta ⊆
      closure (Metric.ball (0 : PhysicalL2) D.delta ∩
        {u : PhysicalL2 | {n : ℤ | actualGapLowerAllE02_38 u n <
          actualGapUpperAllE02_38 u n}.Finite}) := by
  intro D
  exact ⟨D.delta_pos, D.e_forward, D.Phi_action, D.source_ball, D.target_ball,
    D.chart_ball, D.finite_gap_closure⟩

end
end NlsGge.Atomic.ExistingPhysicalFamily
