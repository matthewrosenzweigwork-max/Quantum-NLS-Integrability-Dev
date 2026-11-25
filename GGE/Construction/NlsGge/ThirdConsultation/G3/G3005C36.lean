import Mathlib
import Armstrong.Frozen.RawBeta.gkBetaSourceWellDefined38
import Armstrong.Frozen.RawBetaAnalytic.gkSourceBeta38
import Armstrong.Work.RawBetaActualCoefficient
import Armstrong.Work.RawBetaSum
import NlsGge.Atomic.G2.G2072
import NlsGge.GK38.AbelianPsiNumerator
import NlsGge.ThirdConsultation.G3.G3SourcePathHost
import NlsGge.ThirdConsultation.G3.G3003Host
import NlsGge.ThirdConsultation.G3.G3005UpperHost
import NlsGge.ThirdConsultation.G3.G3005C6Core

                                                                                                                                    
                                                                                         
                                                                                                                               
                                                                                                               
                                                                                                                            
                                                                        
                                                                                                                           
                                                                                                                            
                                                                                        
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G3005C6
noncomputable section

theorem offDiagonalBeta_eq_source' (n m : ℤ) (hmn : m ≠ n) (φ : SourcePotential) :
    offDiagonalBeta n m φ.1 =
      gkSourceBeta38 sourceW sourceFamily.W_open sourceFamily.W_real
        sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
        sourceFamily.F_period n m hmn φ :=
  gk151BetaAmbient_eq_source38 sourceW sourceFamily.W_open sourceFamily.W_real
    sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
    sourceFamily.F_period n m hmn φ

theorem offDiagonalBeta_valueSpec (n m : ℤ) (hmn : m ≠ n) (φ : SourcePotential) :
    GKSourceBetaValue38 n m hmn sourceF (sourceGK φ) (offDiagonalBeta n m φ.1) := by
  have hspec := Classical.choose_spec
    ((gkBetaSourceWellDefined38 sourceW sourceFamily.W_open sourceFamily.W_real
      sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
      sourceFamily.F_period n φ.1 φ.2 m hmn).1)
  rw [offDiagonalBeta_eq_source' n m hmn φ]
  exact hspec.1

theorem chainLim_of_source (n m : ℤ) (φ : SourcePotential) (p : SourcePath m φ) (a : ℂ)
    (hp : HasGKImproperPathIntegral38 n m sourceF (sourceGK φ) p a) :
    ChainLim n m sourceF (sourceGK φ) p.1.1 p.1.2.1 p.1.2.2 (lamMinus φ.1 m) a :=
  ⟨p.2.2.1, hp.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2, hp.2⟩

theorem chainLim_of_upper (n m : ℤ) (φ : SourcePotential) (q : UpperStartPath m φ) (b : ℂ)
    (hq : HasUpperStartIntegral n m φ q b) :
    ChainLim n m sourceF (sourceGK φ) q.1.1 q.1.2.1 q.1.2.2 (lamPlus φ.1 m) b :=
  ⟨q.2.2.1, hq.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2, hq.2⟩

theorem offdiag_coefficient (n m : ℤ) (hmn : m ≠ n) (φ : SourcePotential) :
    ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)) ∧
      ∀ z ∈ GKOriginalSlit38 (sourceGK φ) m,
        perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
          p6PsiNumerator38 n (sourceF n) φ.1 z := by
  have h0 : abelianPeriod38 m φ.1 (p6PsiNumerator38 n (sourceF n) φ.1) = 0 :=
    (p6PsiNumerator_integrable_and_off_diagonal_periods38 n φ.1 (sourceFamily.W_gk φ.2)
      (sourceF n) (sourceFamily.F_zero n φ.1 φ.2)).2 m (Ne.symm hmn)
  obtain ⟨R, hR, hODE⟩ := rawBetaPsiCoefficientOfZeroPeriod38 n m (sourceF n) φ.1
    (sourceFamily.W_gk φ.2) h0
  exact ⟨R, hR, fun z hz => hODE z hz.1⟩

end
end G3005C6

noncomputable section

theorem g3005_c6 (n m : ℤ) (φ : SourcePotential) (hgap : gap φ.1 m ≠ 0) :
    ∀ (p : SourcePath m φ) (q : UpperStartPath m φ) (a b : ℂ),
      HasGKImproperPathIntegral38 n m sourceF (sourceGK φ) p a →
      HasUpperStartIntegral n m φ q b →
      ∃ k : ℤ, a-b =
        (if m=n then (Real.pi : ℂ) else 0) + (k : ℂ)*(2*(Real.pi : ℂ)) := by
  intro p q a b hp hq
  have h₁ := G3005C6.chainLim_of_source n m φ p a hp
  have h₂ := G3005C6.chainLim_of_upper n m φ q b hq
  by_cases hmn : m = n
  · subst hmn
    have hgap' : lamMinus (sourceGK φ).1 m ≠ lamPlus (sourceGK φ).1 m := by
      intro h
      apply hgap
      exact sub_eq_zero.mpr h.symm
    have hper : abelianPeriod38 m (sourceGK φ).1
        (p6PsiNumerator38 m (sourceF m) (sourceGK φ).1) = 2*(Real.pi : ℂ) :=
      (G2_072 φ.1 φ.2 m).2
    obtain ⟨k, hk⟩ := G3005C6.diag_two_chains m sourceF (sourceGK φ)
      (p2Extend38 m (sourceF m φ.1)) rfl hper hgap' _ _ _ _ _ _ a b h₁ h₂
    refine ⟨k, ?_⟩
    rw [if_pos rfl]
    exact hk
  · obtain ⟨R, hR, hODE⟩ := G3005C6.offdiag_coefficient n m hmn φ
    have hab := G3005C6.offdiag_two_chains n m sourceF (sourceGK φ) R hR hODE
      _ _ _ _ _ _ a b h₁ h₂
    refine ⟨0, ?_⟩
    simp [hmn, hab]

theorem g3005_c3 (n m : ℤ) (φ : SourcePotential) :
    m ≠ n → (muSeq φ.1 m = lamMinus φ.1 m ∨ muSeq φ.1 m = lamPlus φ.1 m) →
      offDiagonalBeta n m φ.1 = 0 := by
  intro hmn ht
  obtain ⟨p, hp, -⟩ := G3005C6.offDiagonalBeta_valueSpec n m hmn φ
  have h₁ := G3005C6.chainLim_of_source n m φ p _ hp
  obtain ⟨R, hR, hODE⟩ := G3005C6.offdiag_coefficient n m hmn φ
  rw [G3005C6.offdiag_of_chainLim n m sourceF (sourceGK φ) R hR hODE _ _ _ _ _
    (rawBetaPerCharLowerTipZero38 (sourceGK φ) m) h₁,
    G3005C6.antiDiscrim_tip_zero (sourceGK φ) m ht, zero_mul]

end
end NlsGge.GKDefinitionDesign
