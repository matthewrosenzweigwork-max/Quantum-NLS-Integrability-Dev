import Armstrong.Frozen.RawBetaAnalytic.gkSourceBeta38

set_option autoImplicit false
open Set NlsGge NlsGge.GK38
namespace Armstrong.Providers.RawBetaValue
noncomputable section

theorem gkSourceBeta_characterization38
    (W : Set PotPair := by assumption)
    (hWopen : IsOpen W := by assumption)
    (hreal : range realSlice ⊆ W := by assumption)
    (hWgk : W ⊆ gkW := by assumption)
    (F : (n : ℤ) → PotPair → P2Space38 n := by assumption)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W := by assumption)
    (hFn : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W →
      p2Fn38 n (φ, F n φ) = 0 := by assumption)
    (hperiod : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W → ∀ m : ℤ,
      abelianPeriod38 m φ (p6PsiNumerator38 n (F n) φ) =
        if m = n then 2 * (Real.pi : ℂ) else 0 := by assumption) :
    ∀ n m : ℤ, ∀ hmn : m ≠ n,
      ∀ φ : {ψ : PotPair // ψ ∈ W},
        GKSourceBetaValue38 n m hmn F ⟨φ.1, hWgk φ.2⟩
          (gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m hmn φ) ∧
        (∀ β : ℂ,
          GKSourceBetaValue38 n m hmn F ⟨φ.1, hWgk φ.2⟩ β →
          β = gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m hmn φ) ∧
        ((muSeq φ.1 m = lamMinus φ.1 m ∨
            muSeq φ.1 m = lamPlus φ.1 m) →
          gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m hmn φ = 0) := by
  intro n m hmn φ
  have h := gkBetaSourceWellDefined38 W hWopen hreal hWgk F
    hFanalytic hFn hperiod n φ.1 φ.2 m hmn
  exact ⟨(Classical.choose_spec h.1).1,
    (Classical.choose_spec h.1).2,
    h.2 _ (Classical.choose_spec h.1).1⟩

end
end Armstrong.Providers.RawBetaValue
