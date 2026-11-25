import NlsGge.GK38.AbelianMissingPeriodNormalization
import NlsGge.GK38.AbelianActualPsiFamily

/-! SOURCE ONLY: the actual missing psi period from original-family finite
excision and the genuine large-circle limit. The finite-excision/normalization import
remains uncompiled. No native scope or normalization oracle is asserted. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6PsiNumerator_missing_period38 (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (F : PotPair → P2Space38 n) (hzero : p2Fn38 n (φ,F φ)=0) :
    CircleIntegrable (fun z : ℂ => p6PsiNumerator38 n F φ z/canonRoot38 φ z)
      (discC φ n) (discR φ n) ∧
    abelianPeriod38 n φ (p6PsiNumerator38 n F φ)=2*(Real.pi : ℂ) := by
  obtain ⟨hCI,hperiods⟩ := p6PsiNumerator_integrable_and_off_diagonal_periods38
    n φ hφ F hzero
  refine ⟨hCI n,?_⟩
  have hmissing := p6Actual_missing_period_two_pi38 φ hφ
    (discC φ) (discR φ) (isolating_family38 φ hφ) n (p2Extend38 n (F φ))
    (fun m hm => hperiods m (Ne.symm hm))
  exact hmissing

theorem p6Actual_common_complex_psi_family_normalized_periods38 :
    ∃ W : Set PotPair, IsOpen W ∧ range realSlice ⊆ W ∧ W ⊆ gkW ∧
      ∀ n : ℤ, ∃ F : PotPair → P2Space38 n, AnalyticOnNhd ℂ F W ∧
        AnalyticOnNhd ℂ (fun p : PotPair × ℂ => p6PsiNumerator38 n F p.1 p.2)
          (W ×ˢ (univ : Set ℂ)) ∧
        (∀ φ ∈ W, p2Fn38 n (φ,F φ)=0 ∧
          AnalyticOnNhd ℂ (p6PsiNumerator38 n F φ) univ ∧
          (∀ m : ℤ, CircleIntegrable
            (fun z => p6PsiNumerator38 n F φ z/canonRoot38 φ z) (discC φ m) (discR φ m)) ∧
          ∀ m : ℤ, abelianPeriod38 m φ (p6PsiNumerator38 n F φ)=
            if m=n then 2*(Real.pi : ℂ) else 0) ∧
        ∀ u : PhysicalL2, ∃ t : P3RealSpace38 n,
          t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0 ∧
          F (realSlice u)=p3RealInclude38 n t := by
  obtain ⟨W,hW,hreal,hWg,hbranches⟩ := p6Actual_common_complex_psi_family_off_diagonal38
  refine ⟨W,hW,hreal,hWg,?_⟩
  intro n
  obtain ⟨F,hFa,hjoint,hF,hrealtrace⟩ := hbranches n
  refine ⟨F,hFa,hjoint,?_,hrealtrace⟩
  intro φ hφ
  obtain ⟨hz,hentire,hCI,hperiods⟩ := hF φ hφ
  refine ⟨hz,hentire,hCI,?_⟩
  intro m
  by_cases hm : m=n
  · subst m
    rw [ite_eq_left rfl]
    exact (p6PsiNumerator_missing_period38 n φ (hWg hφ) F hz).2
  · rw [ite_eq_right hm]
    exact hperiods m (Ne.symm hm)

end
end NlsGge.GK38
