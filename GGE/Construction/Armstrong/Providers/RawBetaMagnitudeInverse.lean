import Armstrong.Work.RawBetaMagnitudeInverseProof

set_option autoImplicit false
open Set Metric
open NlsGge.Pilot

namespace Armstrong.Providers.RawBetaMagnitudeInverse
open NlsGge.GK38
noncomputable section

theorem gkSourceBeta_inverseDistance_bound38
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
                hFanalytic hFn hperiod n m hmn psi‖ ≤
              C * (‖lamPlus psi.1 m - lamMinus psi.1 m‖ +
                ‖muSeq psi.1 m - tauN psi.1 m‖) * Lib.c3w n m := by
  exact gk151_inverseDistance_bound_working38
    W hWopen hreal hWgk F hFanalytic hFn hFinv hperiod hFreal

end
end Armstrong.Providers.RawBetaMagnitudeInverse
