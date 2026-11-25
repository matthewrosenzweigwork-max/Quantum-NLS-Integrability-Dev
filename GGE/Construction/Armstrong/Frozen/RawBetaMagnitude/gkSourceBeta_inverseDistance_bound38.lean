-- FROZEN_ANCHOR_PREFIX_BEGIN
import Armstrong.Providers.RawBetaMagnitudeInverse
import Armstrong.Frozen.RawBetaAnalytic.gkSourceBeta_characterization38
import NlsGge.GK38.AbelianPsiTheorem141
import NlsGge.GK38.Lib.EntireProductsC34b

set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem gkSourceBeta_inverseDistance_bound38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W →
      p2Fn38 n (φ, F n φ) = 0)
    (hFinv : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W →
      (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (φ,y)) (F n φ)).IsInvertible)
    (hperiod : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W → ∀ m : ℤ,
      abelianPeriod38 m φ (p6PsiNumerator38 n (F n) φ) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t) :
    ∃ Wbeta : Set PotPair,
      IsOpen Wbeta ∧ range realSlice ⊆ Wbeta ∧ Wbeta ⊆ W ∧
      ∀ φ : PotPair, φ ∈ Wbeta →
        ∃ V : Set PotPair, ∃ C : ℝ,
          IsOpen V ∧ φ ∈ V ∧ V ⊆ Wbeta ∧ 0 < C ∧
          ∀ ψ : {χ : PotPair // χ ∈ W}, ψ.1 ∈ V →
            ∀ n m : ℤ, ∀ hmn : m ≠ n,
              ‖gkSourceBeta38 W hWopen hreal hWgk F
                hFanalytic hFn hperiod n m hmn ψ‖ ≤
              C * (‖lamPlus ψ.1 m - lamMinus ψ.1 m‖ +
                ‖muSeq ψ.1 m - tauN ψ.1 m‖) * Lib.c3w n m :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact Armstrong.Providers.RawBetaMagnitudeInverse.gkSourceBeta_inverseDistance_bound38 W hWopen hreal hWgk F hFanalytic hFn hFinv hperiod hFreal
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN
end
end NlsGge.GK38
-- FROZEN_ANCHOR_SUFFIX_END
