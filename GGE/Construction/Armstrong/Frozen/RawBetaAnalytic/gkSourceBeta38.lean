import Armstrong.Frozen.RawBeta.gkBetaSourceWellDefined38

set_option autoImplicit false
open Set
namespace NlsGge.GK38
noncomputable section

def gkSourceBeta38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W →
      p2Fn38 n (φ, F n φ) = 0)
    (hperiod : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W → ∀ m : ℤ,
      abelianPeriod38 m φ (p6PsiNumerator38 n (F n) φ) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (n m : ℤ) (hmn : m ≠ n)
    (φ : {ψ : PotPair // ψ ∈ W}) : ℂ :=
  Classical.choose
    ((gkBetaSourceWellDefined38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod n φ.1 φ.2 m hmn).1)

end
end NlsGge.GK38
