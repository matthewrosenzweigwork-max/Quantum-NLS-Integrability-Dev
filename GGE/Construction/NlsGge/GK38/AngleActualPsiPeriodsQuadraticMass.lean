import NlsGge.GK38.AngleActualGlobalQuadraticMass
import NlsGge.GK38.AbelianPsiPeriodNormalization

/-! Source-only combined witness for the SAME actual mass-controlled normalized
psi family. Existing preferred psi APIs are unchanged. Actual Fn zeros earn
all periods, and the literal quadratic root identity earns the collapsed node.
No all-coordinate original-disc placement premise is introduced. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem angleActual_same_psi_periods_quadratic_mass_collapsed_nodes38 :
    ∃ W : Set PotPair, IsOpen W ∧ range realSlice ⊆ W ∧ W ⊆ gkW ∧
      ∃ F : (n : ℤ) → PotPair → P2Space38 n,
        (∀ n : ℤ, AnalyticOnNhd ℂ (F n) W) ∧
        (∀ n : ℤ, ∀ φ ∈ W, p2Fn38 n (φ,F n φ)=0 ∧
          (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (φ,y)) (F n φ)).IsInvertible) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ
          (fun p : PotPair × ℂ => p6PsiNumerator38 n (F n) p.1 p.2)
          (W ×ˢ (univ : Set ℂ))) ∧
        (∀ n : ℤ, ∀ φ ∈ W, ∀ m : ℤ,
          CircleIntegrable (fun z : ℂ => p6PsiNumerator38 n (F n) φ z/canonRoot38 φ z)
            (discC φ m) (discR φ m) ∧
          abelianPeriod38 m φ (p6PsiNumerator38 n (F n) φ)=
            if m=n then 2*(Real.pi : ℂ) else 0) ∧
        (∀ n : ℤ, ∀ u : PhysicalL2, ∃ t : P3RealSpace38 n,
          t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0 ∧
          F n (realSlice u)=p3RealInclude38 n t) ∧
        (∀ φ ∈ W, ∃ r B : ℝ, 0 < r ∧ 0 < B ∧ ball φ r ⊆ W ∧
          ∀ ψ ∈ ball φ r, ∀ n : ℤ, ∃ A : P2Space38 n,
            (∀ m : P2Index38 n,
              A m=(countingCenter38 m.1+F n ψ m-tauN ψ m.1)/gamma2 ψ m.1) ∧
            Summable (fun m : P2Index38 n => ‖A m‖^2) ∧
            (∑' m : P2Index38 n,‖A m‖^2) ≤ B ∧
            ∀ m : P2Index38 n,
              countingCenter38 m.1+F n ψ m=tauN ψ m.1+gamma2 ψ m.1*A m) ∧
        ∀ n : ℤ, ∀ φ ∈ W, ∀ m : ℤ, ∀ hmn : m ≠ n,
          gamma2 φ m=0 →
            countingCenter38 m+F n φ ⟨m,hmn⟩=tauN φ m := by
  obtain ⟨W,hW,hreal,hWW,F,hFa,hFspec,hFreal,hMass⟩ :=
    angleActual_global_normalized_locally_uniform_quadratic_quotients38
  refine ⟨W,hW,hreal,hWW,F,hFa,hFspec,
    fun n => p6PsiNumerator_joint_analytic38 n W (F n) (hFa n),?_,hFreal,hMass,?_⟩
  · intro n φ hφ m
    obtain ⟨hCI,hOff⟩ := p6PsiNumerator_integrable_and_off_diagonal_periods38
      n φ (hWW hφ) (F n) (hFspec n φ hφ).1
    refine ⟨hCI m,?_⟩
    by_cases hm : m=n
    · subst m
      rw [ite_eq_left rfl]
      exact (p6PsiNumerator_missing_period38 n φ (hWW hφ) (F n)
        (hFspec n φ hφ).1).2
    · rw [ite_eq_right hm]
      exact hOff m (Ne.symm hm)
  · intro n φ hφ m hmn hgap
    obtain ⟨r,B,hr,_hB,_hball,hbound⟩ := hMass φ hφ
    obtain ⟨A,_hA,_hAs,_hAB,hroot⟩ := hbound φ (mem_ball_self hr) n
    have he := hroot ⟨m,hmn⟩
    simpa only [hgap,zero_mul,add_zero] using he

end
end NlsGge.GK38
