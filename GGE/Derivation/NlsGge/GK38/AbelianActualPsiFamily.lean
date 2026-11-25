import NlsGge.GK38.AbelianActualCommonComplexInverseNeighborhood
import NlsGge.GK38.AbelianPsiNumerator

/-! Genuine entire psi-functions from the actual common complex normalized
solution neighborhood. Every off-index period is zero with actual circle
integrability. The n-th period normalization is a separate remaining step. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6Actual_common_complex_psi_family_off_diagonal38 :
    ∃ W : Set PotPair, IsOpen W ∧ range realSlice ⊆ W ∧ W ⊆ gkW ∧
      ∀ n : ℤ, ∃ F : PotPair → P2Space38 n, AnalyticOnNhd ℂ F W ∧
        AnalyticOnNhd ℂ (fun p : PotPair × ℂ => p6PsiNumerator38 n F p.1 p.2)
          (W ×ˢ (univ : Set ℂ)) ∧
        (∀ φ ∈ W, p2Fn38 n (φ,F φ)=0 ∧
          AnalyticOnNhd ℂ (p6PsiNumerator38 n F φ) univ ∧
          (∀ m : ℤ, CircleIntegrable
            (fun z => p6PsiNumerator38 n F φ z/canonRoot38 φ z) (discC φ m) (discR φ m)) ∧
          ∀ m : ℤ, n ≠ m → abelianPeriod38 m φ (p6PsiNumerator38 n F φ)=0) ∧
        ∀ u : PhysicalL2, ∃ t : P3RealSpace38 n,
          t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0 ∧
          F (realSlice u)=p3RealInclude38 n t := by
  obtain ⟨W,hW,hreal,hWg,hbranches⟩ := p6Actual_common_complex_normalized_inverse_neighborhood38
  refine ⟨W,hW,hreal,hWg,?_⟩
  intro n
  obtain ⟨F,hFa,hFz,hFreal⟩ := hbranches n
  refine ⟨F,hFa,p6PsiNumerator_joint_analytic38 n W F hFa,?_,hFreal⟩
  intro φ hφ
  obtain ⟨hCI,hperiods⟩ := p6PsiNumerator_integrable_and_off_diagonal_periods38
    n φ (hWg hφ) F (hFz φ hφ).1
  exact ⟨(hFz φ hφ).1,p6PsiNumerator_entire38 n F φ,hCI,hperiods⟩

end
end NlsGge.GK38
