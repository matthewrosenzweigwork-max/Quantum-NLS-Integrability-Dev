-- FROZEN_ANCHOR_PREFIX_BEGIN
import Armstrong.Frozen.RawBetaAnalytic.gkSourceBeta_characterization38
import Armstrong.Providers.RawBetaAnalytic

set_option autoImplicit false
open Set
namespace NlsGge.GK38
noncomputable section

theorem gkSourceBeta_analytic38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W →
      p2Fn38 n (φ, F n φ) = 0)
    (hperiod : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W → ∀ m : ℤ,
      abelianPeriod38 m φ (p6PsiNumerator38 n (F n) φ) =
        if m = n then 2 * (Real.pi : ℂ) else 0) :
    ∀ n m : ℤ, ∀ hmn : m ≠ n,
      ∃ b : PotPair → ℂ,
        AnalyticOnNhd ℂ b W ∧
        ∀ φ : {ψ : PotPair // ψ ∈ W},
          b φ.1 =
            gkSourceBeta38 W hWopen hreal hWgk F
              hFanalytic hFn hperiod n m hmn φ
  :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact Armstrong.Providers.RawBetaAnalytic.gkSourceBeta_analytic38
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end
end NlsGge.GK38
-- FROZEN_ANCHOR_SUFFIX_END
