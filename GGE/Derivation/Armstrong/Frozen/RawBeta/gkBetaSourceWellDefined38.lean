-- FROZEN_ANCHOR_PREFIX_BEGIN
import Armstrong.Frozen.RawBeta.GKSourceBetaValue38
import Armstrong.Providers.RawBeta

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

theorem gkBetaSourceWellDefined38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W →
      p2Fn38 n (φ, F n φ) = 0)
    (hperiod : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W → ∀ m : ℤ,
      abelianPeriod38 m φ (p6PsiNumerator38 n (F n) φ) =
        if m = n then 2 * (Real.pi : ℂ) else 0) :
    ∀ n : ℤ, ∀ φ : PotPair, ∀ hφ : φ ∈ W,
      ∀ m : ℤ, ∀ hmn : m ≠ n,
        (∃! β : ℂ,
          GKSourceBetaValue38 n m hmn F ⟨φ, hWgk hφ⟩ β) ∧
        (∀ β : ℂ,
          GKSourceBetaValue38 n m hmn F ⟨φ, hWgk hφ⟩ β →
          (muSeq φ m = lamMinus φ m ∨ muSeq φ m = lamPlus φ m) → β = 0)
  :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact Armstrong.Providers.RawBeta.gkBetaSourceWellDefined38
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end
end NlsGge.GK38
-- FROZEN_ANCHOR_SUFFIX_END
