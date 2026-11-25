import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5024
import NlsGge.Atomic.G5.G5023
import NlsGge.ThirdConsultation.G5.Basic
import NlsGge.Atomic.G5.G5031Sup1
import NlsGge.Atomic.G5.G5031Sup2
import NlsGge.Atomic.G5.G5031Sup3
import NlsGge.Atomic.G5.G5032Sup1
import NlsGge.Atomic.LIB.LIB081
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.GK38.AbelianPsiNumerator

                                                                                       
                                                                                         
                                                                                                                   
                                                                                                                                               
                                                                                                                                     
                                                                                                                   
                                                                                                                    
                  
                                                                                                                                 
                                                                                                                                    
                                                                                                                                          
                                                                                                       
                                                                                                     
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.Atomic.LIB

namespace NlsGge.GKDefinitionDesign
namespace G5035Sup1
noncomputable section

/-- Circle decay is preserved by the half-difference. -/
theorem circleRatio_half_sub {f h g : ℂ → ℂ} (hf : CircleRatioTendstoZero f g)
    (hh : CircleRatioTendstoZero h g) :
    CircleRatioTendstoZero (fun z => (f z - h z) / 2) g := by
  intro ε hε
  obtain ⟨N₁, h₁⟩ := hf ε hε
  obtain ⟨N₂, h₂⟩ := hh ε hε
  refine ⟨max N₁ N₂, fun R hR z hz => ?_⟩
  have a := h₁ R ((le_max_left _ _).trans hR) z hz
  have b := h₂ R ((le_max_right _ _).trans hR) z hz
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_div, h2, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have := norm_sub_le (f z) (h z)
  have hg : 0 ≤ ε * ‖g z‖ := mul_nonneg hε.le (norm_nonneg _)
  linarith

theorem analyticAt_discrim_lam (lam : ℂ) (φ : PotPair) :
    AnalyticAt ℂ (fun ψ : PotPair => discrim ψ lam) φ := by
  have hc : AnalyticAt ℂ (fun ψ : PotPair => ((ψ, lam) : PotPair × ℂ)) φ :=
    analyticAt_id.prod analyticAt_const
  have h := AnalyticAt.comp (g := fun p : PotPair × ℂ => discrim p.1 p.2)
    (f := fun ψ : PotPair => ((ψ, lam) : PotPair × ℂ)) (analyticOnNhd_discrim (φ, lam) (mem_univ _)) hc
  exact h

/-- `psi_n(lam)` is complex analytic in the potential at every real point. -/
theorem analyticAt_psiAt (n : ℤ) (lam : ℂ) (u : PhysicalL2) :
    AnalyticAt ℂ (psiAt n lam) (realSlice u) := by
  have hB : realSlice u ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u)
  have hJ := p6PsiNumerator_joint_analytic38 n sourceW (sourceF n) (sourceFamily.F_analytic n)
    (realSlice u, lam) ⟨sourceFamily.V_W hB, Set.mem_univ _⟩
  have hc : AnalyticAt ℂ (fun ψ : PotPair => ((ψ, lam) : PotPair × ℂ)) (realSlice u) :=
    analyticAt_id.prod analyticAt_const
  have h := AnalyticAt.comp (g := fun p : PotPair × ℂ => p6PsiNumerator38 n (sourceF n) p.1 p.2)
    (f := fun ψ : PotPair => ((ψ, lam) : PotPair × ℂ)) hJ hc
  exact h

/-- `2 {Delta_lam, theta_j}` and `psi_j(lam)` have equal complex derivatives at the real point. -/
theorem fderiv_bracket_psi (u : PhysicalL2) (j : ℤ) (lam : ℂ)
    (hj : gamma2 (realSlice u) j ≠ 0)
    (h25 : ∀ w : PhysicalL2, gamma2 (realSlice w) j ≠ 0 →
      2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice w))
        (angleDerivative j (realSlice w)) = psiAt j lam (realSlice w))
    (V : Set PotPair) (θ : PotPair → ℂ) (hV : IsOpen V) (hx : realSlice u ∈ V)
    (han : AnalyticOnNhd ℂ θ V) (hd : ∀ ψ ∈ V, fderiv ℂ θ ψ = angleDerivative j ψ)
    (v : PotPair) :
    2 * fderiv ℂ (constantPoisson G5031Sup3.Jmap (fun ψ => discrim ψ lam) θ) (realSlice u) v =
      fderiv ℂ (psiAt j lam) (realSlice u) v := by
  have hcD : ContDiffAt ℂ 2 (fun ψ : PotPair => discrim ψ lam) (realSlice u) :=
    (analyticAt_discrim_lam lam _).contDiffAt
  have hcθ : ContDiffAt ℂ 2 θ (realSlice u) := (han _ hx).contDiffAt
  have hPd : DifferentiableAt ℂ
      (constantPoisson G5031Sup3.Jmap (fun ψ => discrim ψ lam) θ) (realSlice u) :=
    G5031Sup3.differentiableAt_constantPoisson hcD hcθ
  have hψd : DifferentiableAt ℂ (psiAt j lam) (realSlice u) :=
    (analyticAt_psiAt j lam u).differentiableAt
  have hevV : ∀ᶠ w in 𝓝 u, realSlice w ∈ V :=
    realSlice.continuous.continuousAt.eventually (hV.mem_nhds hx)
  have hzero := G5031Sup2.fderiv_eq_zero_of_real_const
    (fun ψ => 2 * constantPoisson G5031Sup3.Jmap (fun ψ => discrim ψ lam) θ ψ - psiAt j lam ψ) u 0
    ((hPd.const_mul 2).sub hψd) (by
      filter_upwards [hevV, G5031Sup3.eventually_gamma2_ne u j hj] with w hw hwj
      have e1 : constantPoisson G5031Sup3.Jmap (fun ψ => discrim ψ lam) θ (realSlice w) =
          pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice w))
            (angleDerivative j (realSlice w)) := by
        rw [constantPoisson_apply, hd _ hw]
        rfl
      show 2 * constantPoisson G5031Sup3.Jmap (fun ψ => discrim ψ lam) θ (realSlice w) -
        psiAt j lam (realSlice w) = 0
      rw [e1, h25 w hwj, sub_self])
  have e : fderiv ℂ
      (fun ψ => 2 * constantPoisson G5031Sup3.Jmap (fun ψ => discrim ψ lam) θ ψ - psiAt j lam ψ)
      (realSlice u) =
      (2 : ℂ) • fderiv ℂ (constantPoisson G5031Sup3.Jmap (fun ψ => discrim ψ lam) θ) (realSlice u) -
        fderiv ℂ (psiAt j lam) (realSlice u) := by
    rw [fderiv_fun_sub (hPd.const_mul 2) hψd, fderiv_const_mul hPd]
  rw [e] at hzero
  have h := congrArg (fun L : PotPair →L[ℂ] ℂ => L v) hzero
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.zero_apply] at h
  linear_combination h

/-- GK 18.6 (Jacobi step): the double bracket in terms of the two psi-angle brackets. -/
theorem bracket_formula (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0) (lam : ℂ)
    (hprim : ∀ (w : PhysicalL2) (j : ℤ), gamma2 (realSlice w) j ≠ 0 →
      ∃ (V : Set PotPair) (θ : PotPair → ℂ), IsOpen V ∧ realSlice w ∈ V ∧
        AnalyticOnNhd ℂ θ V ∧ ∀ ψ ∈ V, fderiv ℂ θ ψ = angleDerivative j ψ)
    (h25 : ∀ (w : PhysicalL2) (j : ℤ), gamma2 (realSlice w) j ≠ 0 → ∀ lam : ℂ,
      2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice w))
        (angleDerivative j (realSlice w)) = psiAt j lam (realSlice w)) :
    doubleAngleDiscriminantBracket m n (realSlice u) lam =
      (pairPoissonCLM (fderiv ℂ (psiAt m lam) (realSlice u)) (angleDerivative n (realSlice u)) -
        pairPoissonCLM (fderiv ℂ (psiAt n lam) (realSlice u))
          (angleDerivative m (realSlice u))) / 2 := by
  obtain ⟨Vm, θm, hVm, hxm, hanm, hdm⟩ := hprim u m hm
  obtain ⟨Vn, θn, hVn, hxn, hann, hdn⟩ := hprim u n hn
  have hcD : ContDiffAt ℂ 2 (fun ψ : PotPair => discrim ψ lam) (realSlice u) :=
    (analyticAt_discrim_lam lam _).contDiffAt
  have hcm : ContDiffAt ℂ 2 θm (realSlice u) := (hanm _ hxm).contDiffAt
  have hcn : ContDiffAt ℂ 2 θn (realSlice u) := (hann _ hxn).contDiffAt
  have hVo : IsOpen (Vm ∩ Vn) := hVm.inter hVn
  have hxV : realSlice u ∈ Vm ∩ Vn := ⟨hxm, hxn⟩
  have hPeq : anglePoisson m n =ᶠ[𝓝 (realSlice u)] constantPoisson G5031Sup3.Jmap θm θn := by
    filter_upwards [hVo.mem_nhds hxV] with ψ hψ
    simp only [anglePoisson, constantPoisson_apply, hdm ψ hψ.1, hdn ψ hψ.2]
    rfl
  have hJac := G5031Sup1.constantPoisson_jacobi_at G5031Sup3.Jmap G5031Sup3.isSkew_Jmap
    (fun ψ : PotPair => discrim ψ lam) θm θn (realSlice u) hcD hcm hcn
  -- first Jacobi term
  have T1 : 2 * constantPoisson G5031Sup3.Jmap
      (constantPoisson G5031Sup3.Jmap (fun ψ : PotPair => discrim ψ lam) θm) θn (realSlice u) =
      pairPoissonCLM (fderiv ℂ (psiAt m lam) (realSlice u)) (angleDerivative n (realSlice u)) := by
    rw [constantPoisson_apply, hdn _ hxn]
    exact fderiv_bracket_psi u m lam hm (fun w hw => h25 w m hw lam) Vm θm hVm hxm hanm hdm
      (G5031Sup3.Jmap (angleDerivative n (realSlice u)))
  -- third Jacobi term: {theta_n, Delta} = -{Delta, theta_n}
  have hskewfun : constantPoisson G5031Sup3.Jmap θn (fun ψ : PotPair => discrim ψ lam) =
      fun ψ => -constantPoisson G5031Sup3.Jmap (fun ψ : PotPair => discrim ψ lam) θn ψ := by
    funext ψ
    rw [constantPoisson_apply, constantPoisson_apply]
    exact G5031Sup3.isSkew_Jmap _ _
  have T3 : 2 * constantPoisson G5031Sup3.Jmap
      (constantPoisson G5031Sup3.Jmap θn (fun ψ : PotPair => discrim ψ lam)) θm (realSlice u) =
      -pairPoissonCLM (fderiv ℂ (psiAt n lam) (realSlice u)) (angleDerivative m (realSlice u)) := by
    rw [constantPoisson_apply, hdm _ hxm, hskewfun, fderiv_fun_neg]
    have h := fderiv_bracket_psi u n lam hn (fun w hw => h25 w n hw lam) Vn θn hVn hxn hann hdn
      (G5031Sup3.Jmap (angleDerivative m (realSlice u)))
    rw [ContinuousLinearMap.neg_apply]
    show 2 * -(fderiv ℂ (constantPoisson G5031Sup3.Jmap (fun ψ : PotPair => discrim ψ lam) θn)
      (realSlice u) (G5031Sup3.Jmap (angleDerivative m (realSlice u)))) =
      -(fderiv ℂ (psiAt n lam) (realSlice u) (G5031Sup3.Jmap (angleDerivative m (realSlice u))))
    rw [← h]
    ring
  -- second Jacobi term: {{theta_m,theta_n}, Delta} = -{Delta,{theta_m,theta_n}}
  have T2 : constantPoisson G5031Sup3.Jmap (constantPoisson G5031Sup3.Jmap θm θn)
      (fun ψ : PotPair => discrim ψ lam) (realSlice u) =
      -doubleAngleDiscriminantBracket m n (realSlice u) lam := by
    rw [constantPoisson_apply, ← hPeq.fderiv_eq]
    exact G5031Sup3.isSkew_Jmap _ _
  linear_combination (1 / 2 : ℂ) * T1 + (1 / 2 : ℂ) * T3 + T2 - hJac

/-- GK 18.6: the double bracket vanishes identically (landed inputs as parameters). -/
theorem core35 (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0)
    (hprim : ∀ (w : PhysicalL2) (j : ℤ), gamma2 (realSlice w) j ≠ 0 →
      ∃ (V : Set PotPair) (θ : PotPair → ℂ), IsOpen V ∧ realSlice w ∈ V ∧
        AnalyticOnNhd ℂ θ V ∧ ∀ ψ ∈ V, fderiv ℂ θ ψ = angleDerivative j ψ)
    (h25 : ∀ (w : PhysicalL2) (j : ℤ), gamma2 (realSlice w) j ≠ 0 → ∀ lam : ℂ,
      2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice w))
        (angleDerivative j (realSlice w)) = psiAt j lam (realSlice w))
    (h32 : ∃ ν : ℤ → ℝ, Function.Injective ν ∧
      (∀ k : ℤ, ν k ∈ Set.Icc (actualGapLowerAllE02_38 u k)
        (actualGapUpperAllE02_38 u k) ∧
        doubleAngleDiscriminantBracket m n (realSlice u) (ν k : ℂ) = 0) ∧
      Memℓp (fun k : ℤ => ν k - (k : ℝ) * Real.pi) 2)
    (h34 : ∀ i j : ℤ, gamma2 (realSlice u) i ≠ 0 →
      CircleRatioTendstoZero
        (fun z => pairPoissonCLM (fderiv ℂ (psiAt j z) (realSlice u))
          (angleDerivative i (realSlice u))) Complex.sin) :
    ∀ lam : ℂ, doubleAngleDiscriminantBracket m n (realSlice u) lam = 0 := by
  intro lam
  obtain ⟨ν, hinj, hroot, hmem⟩ := h32
  have hdiff : Differentiable ℂ (doubleAngleDiscriminantBracket m n (realSlice u)) := fun z =>
    (G5032Sup1.doubleBracket_analytic m n (realSlice u) z (mem_univ _)).differentiableAt
  have hdecay : CircleRatioTendstoZero (doubleAngleDiscriminantBracket m n (realSlice u))
      Complex.sin := by
    have h := circleRatio_half_sub (h34 n m hn) (h34 m n hm)
    have e : doubleAngleDiscriminantBracket m n (realSlice u) = fun z =>
        (pairPoissonCLM (fderiv ℂ (psiAt m z) (realSlice u)) (angleDerivative n (realSlice u)) -
          pairPoissonCLM (fderiv ℂ (psiAt n z) (realSlice u))
            (angleDerivative m (realSlice u))) / 2 :=
      funext fun z => bracket_formula u m n hm hn z hprim h25
    rw [e]
    exact h
  have h2 := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mp hmem
  have h2' : Summable (fun k : ℤ => ‖ν k - (k : ℝ) * Real.pi‖ ^ 2) := by simpa using h2
  have hσ : Summable (fun k : ℤ => ‖((ν k : ℝ) : ℂ) - (k : ℂ) * Real.pi‖ ^ 2) := by
    refine h2'.congr fun k => ?_
    have e : ((ν k : ℝ) : ℂ) - (k : ℂ) * Real.pi = ((ν k - (k : ℝ) * Real.pi : ℝ) : ℂ) := by
      push_cast
      try ring
    rw [e, Complex.norm_real]
  have hinjC : Function.Injective (fun k : ℤ => ((ν k : ℝ) : ℂ)) :=
    Complex.ofReal_injective.comp hinj
  have hI := (G5023 (fun k : ℤ => ((ν k : ℝ) : ℂ)) (doubleAngleDiscriminantBracket m n (realSlice u))
    lam hσ hinjC hdiff hdecay).2.2
  have hI' : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop
      (𝓝 (doubleAngleDiscriminantBracket m n (realSlice u) lam)) :=
    Tendsto.congr (fun R => Finset.sum_eq_zero fun j _ => by
      show doubleAngleDiscriminantBracket m n (realSlice u) ((ν j : ℝ) : ℂ) * _ = 0
      rw [(hroot j).2, zero_mul]) hI
  exact tendsto_nhds_unique hI' tendsto_const_nhds

end
end G5035Sup1
end NlsGge.GKDefinitionDesign
