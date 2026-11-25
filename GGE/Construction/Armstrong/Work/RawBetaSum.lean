import Armstrong.Work.RawBetaMagnitudeInverseProof
import Armstrong.Work.RawBetaSumSpectralMass
import Armstrong.Frozen.RawBetaAnalytic.gkSourceBeta_analytic38
import NlsGge.GK38.Lib.InverseDistanceAnalyticSeries

/-!
# Summed off-diagonal source beta

Working formalization of the beta-series part of GK Theorem 15.3.
The diagonal is defined to be zero, while off-diagonal entries use the accepted
ambient analytic representatives of the genuine source beta.
-/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

noncomputable def gk151BetaAmbient38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (n m : ℤ) : PotPair → ℂ :=
  if h : m = n then fun _ => 0
  else Classical.choose
    (gkSourceBeta_analytic38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod n m h)

theorem gk151BetaAmbient_analytic38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (n m : ℤ) :
    AnalyticOnNhd ℂ
      (gk151BetaAmbient38 W hWopen hreal hWgk F
        hFanalytic hFn hperiod n m) W := by
  by_cases h : m = n
  · rw [gk151BetaAmbient38, dite_eq_left h]
    exact analyticOnNhd_const
  · rw [gk151BetaAmbient38, dite_eq_right h]
    exact (Classical.choose_spec
      (gkSourceBeta_analytic38 W hWopen hreal hWgk F
        hFanalytic hFn hperiod n m h)).1

theorem gk151BetaAmbient_eq_source38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (n m : ℤ) (hmn : m ≠ n) (phi : {psi : PotPair // psi ∈ W}) :
    gk151BetaAmbient38 W hWopen hreal hWgk F
        hFanalytic hFn hperiod n m phi.1 =
      gkSourceBeta38 W hWopen hreal hWgk F
        hFanalytic hFn hperiod n m hmn phi := by
  rw [gk151BetaAmbient38, dite_eq_right hmn]
  exact (Classical.choose_spec
    (gkSourceBeta_analytic38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod n m hmn)).2 phi

theorem gk151BetaAmbient_diag38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (n : ℤ) :
    gk151BetaAmbient38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod n n = 0 := by
  funext phi
  simp [gk151BetaAmbient38]

noncomputable def gk151BetaSum38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (n : ℤ) (phi : PotPair) : ℂ :=
  ∑' m : ℤ, gk151BetaAmbient38 W hWopen hreal hWgk F
    hFanalytic hFn hperiod n m phi

theorem gk151_beta_series38
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
        F n (realSlice u) = p3RealInclude38 n t) :
    ∃ Wbeta : Set PotPair,
      IsOpen Wbeta ∧ range realSlice ⊆ Wbeta ∧ Wbeta ⊆ W ∧
      (∀ n : ℤ, ∀ phi ∈ Wbeta,
        Summable (fun m : ℤ =>
          ‖gk151BetaAmbient38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m phi‖)) ∧
      (∀ n : ℤ,
        HasSumLocallyUniformlyOn
          (fun m : ℤ => gk151BetaAmbient38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m)
          (gk151BetaSum38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n) Wbeta) ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ
        (gk151BetaSum38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n) Wbeta) ∧
      (∀ phi ∈ Wbeta, Tendsto
        (fun n : ℤ => gk151BetaSum38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n phi)
        cofinite (𝓝 (0 : ℂ))) := by
  obtain ⟨Wbeta, hWbetaOpen, hrealBeta, hbetaW, hinv⟩ :=
    gk151_inverseDistance_bound_working38
      W hWopen hreal hWgk F hFanalytic hFn hFinv hperiod hFreal
  let b : ℤ → ℤ → PotPair → ℂ :=
    fun n m => gk151BetaAmbient38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod n m
  let a : PotPair → ℤ → ℂ := gk151BetaMass38
  have hb : ∀ n m : ℤ, AnalyticOnNhd ℂ (b n m) Wbeta := by
    intro n m
    exact (gk151BetaAmbient_analytic38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod n m).mono hbetaW
  have hlocal : ∀ x ∈ Wbeta, ∃ V : Set PotPair, ∃ C M : ℝ,
      IsOpen V ∧ x ∈ V ∧ V ⊆ Wbeta ∧ 0 ≤ C ∧ 0 ≤ M ∧
      (∀ y ∈ V,
        Summable (fun m : ℤ => ‖a y m‖^2) ∧
        (∑' m : ℤ, ‖a y m‖^2) ≤ M) ∧
      (∀ y ∈ V, ∀ n m : ℤ,
        ‖b n m y‖ ≤ C * ‖a y m‖ * Lib.c3w n m) := by
    intro x hx
    obtain ⟨Vb, C, hVb, hxVb, hVbW, hC, hbeta⟩ := hinv x hx
    obtain ⟨Us, hUs, hUsGK, M, hM, hmass⟩ :=
      gk151BetaMass_local_l2_38 x (hWgk (hbetaW hx))
    let V : Set PotPair := Vb ∩ interior Us
    have hxi : x ∈ interior Us := mem_interior_iff_mem_nhds.mpr hUs
    refine ⟨V, C, M, hVb.inter isOpen_interior, ⟨hxVb,hxi⟩,
      fun y hy => hVbW hy.1, hC.le, hM, ?_, ?_⟩
    · intro y hy
      exact hmass y (interior_subset hy.2)
    · intro y hy n m
      by_cases hmn : m = n
      · subst m
        simp only [b, gk151BetaAmbient_diag38, Pi.zero_apply, norm_zero]
        exact mul_nonneg (mul_nonneg hC.le (norm_nonneg _))
          (Lib.c3w_nonneg n n)
      · let py : {chi : PotPair // chi ∈ W} :=
          ⟨y, hbetaW (hVbW hy.1)⟩
        have hbound := hbeta py hy.1 n m hmn
        have heq := gk151BetaAmbient_eq_source38
          W hWopen hreal hWgk F hFanalytic hFn hperiod n m hmn py
        rw [← heq] at hbound
        simpa only [b, a, norm_gk151BetaMass38, mul_assoc] using hbound
  have hseries := Lib.inverseDistance_analytic_series38
    Wbeta hWbetaOpen b a hb hlocal
  refine ⟨Wbeta, hWbetaOpen, hrealBeta, hbetaW, ?_, ?_, ?_, ?_⟩
  · simpa only [b] using hseries.1
  · intro n
    change HasSumLocallyUniformlyOn
      (fun m : ℤ => gk151BetaAmbient38 W hWopen hreal hWgk F
        hFanalytic hFn hperiod n m)
      (fun x : PotPair => ∑' m : ℤ,
        gk151BetaAmbient38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m x) Wbeta
    simpa only [b] using hseries.2.1 n
  · intro n
    change AnalyticOnNhd ℂ
      (fun x : PotPair => ∑' m : ℤ,
        gk151BetaAmbient38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m x) Wbeta
    simpa only [b] using hseries.2.2.1 n
  · intro phi hphi
    change Tendsto
      (fun n : ℤ => ∑' m : ℤ,
        gk151BetaAmbient38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m phi)
      cofinite (𝓝 (0 : ℂ))
    simpa only [b] using hseries.2.2.2 phi hphi

end
end NlsGge.GK38
