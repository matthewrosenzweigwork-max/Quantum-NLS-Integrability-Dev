import Armstrong.Work.RawBetaMagnitudeLocalEstimate

/-!
# Global working proof of the frozen GK15.1 nearest-endpoint estimate

This theorem has the frozen target's mathematical type but remains in Work/.
It does not import, edit, or seal the quarantined frozen anchor/provider.
-/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem gk151_nearestEndpoint_bound_working38
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
      ∀ phi : PotPair, phi ∈ Wbeta →
        ∃ V : Set PotPair, ∃ C : ℝ,
          IsOpen V ∧ phi ∈ V ∧ V ⊆ Wbeta ∧ 0 < C ∧
          ∀ psi : {chi : PotPair // chi ∈ W}, psi.1 ∈ V →
            ∀ n m : ℤ, ∀ hmn : m ≠ n,
              ‖gkSourceBeta38 W hWopen hreal hWgk F
                hFanalytic hFn hperiod n m hmn psi‖ <=
              C * Real.sqrt (‖lamPlus psi.1 m - lamMinus psi.1 m‖ +
                min ‖muSeq psi.1 m - lamMinus psi.1 m‖
                  ‖muSeq psi.1 m - lamPlus psi.1 m‖) *
                Real.sqrt (min ‖muSeq psi.1 m - lamMinus psi.1 m‖
                  ‖muSeq psi.1 m - lamPlus psi.1 m‖) * Lib.c3w n m := by
  classical
  choose delta C hdelta hC hsub hbound using
    (fun u : PhysicalL2 =>
      gk151_local_nearestEndpoint_bound38 W hWopen hreal hWgk F
        hFanalytic hFn hFinv hperiod hFreal u)
  let Wbeta : Set PotPair := ⋃ u : PhysicalL2, ball (realSlice u) (delta u)
  have hWopenBeta : IsOpen Wbeta :=
    isOpen_iUnion (fun u => isOpen_ball)
  have hrealBeta : range realSlice ⊆ Wbeta := by
    rintro phi ⟨u, rfl⟩
    exact mem_iUnion.mpr ⟨u, mem_ball_self (hdelta u)⟩
  have hbetaW : Wbeta ⊆ W := by
    intro phi hphi
    obtain ⟨u, hu⟩ := mem_iUnion.mp hphi
    exact hsub u hu
  refine ⟨Wbeta, hWopenBeta, hrealBeta, hbetaW, ?_⟩
  intro phi hphi
  obtain ⟨u, hu⟩ := mem_iUnion.mp hphi
  obtain ⟨r, hr, hrsub⟩ := Metric.exists_ball_subset_ball hu
  refine ⟨ball phi r, C u, isOpen_ball, mem_ball_self hr, ?_, hC u, ?_⟩
  · intro chi hchi
    exact mem_iUnion.mpr ⟨u, hrsub hchi⟩
  · intro psi hpsi n m hmn
    exact hbound u psi (hrsub hpsi) n m hmn

end
end NlsGge.GK38
