import Mathlib
import NlsGge.Ramer.FiniteDivergenceGrowth

                                                                                                                
                                                                                                                    
                                                                                                                    
                                                                                       
                                                                                                               
                                                                                                             
                              
set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- A compactly supported `C¹` field has bounded value and derivative (growth exponent `0`). -/
theorem r021_growth_of_compact {g : V → V} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, (∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ (0 : ℕ)) ∧
      (∀ v, ‖fderiv ℝ g v‖ ≤ C * (1 + ‖v‖) ^ (0 : ℕ)) := by
  obtain ⟨B0, hB0⟩ := hg.continuous.bounded_above_of_compact_support hgc
  obtain ⟨B1, hB1⟩ := (hg.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hgc.fderiv (𝕜 := ℝ))
  refine ⟨max B0 B1, fun v => ?_, fun v => ?_⟩
  · rw [pow_zero, mul_one]; exact (hB0 v).trans (le_max_left _ _)
  · rw [pow_zero, mul_one]; exact (hB1 v).trans (le_max_right _ _)

/-- The cutoff sequence `F_n = χ_{n+1} • F`. -/
abbrev r021Cut (F : V → V) (n : ℕ) : V → V :=
  fun y => NlsGge.Ramer.cutR (V := V) ((n : ℝ) + 1) y • F y

/-- **Finite-head `L²` integration by parts.** For `C²` `F` with `F`, `δF ∈ L²(γ)` and a bounded `C¹`
test function `φ` with bounded derivative, both `φ δF` and `Dφ(F)` are `γ`-integrable and
`∫ φ δF dγ = ∫ Dφ(F) dγ`. -/
theorem r021_ibp_L2 {F : V → V} (hF : ContDiff ℝ 2 F)
    (hFL : MemLp F 2 (NlsGge.Ramer.finiteStdGaussian V))
    (hδL : MemLp (NlsGge.Ramer.finiteGaussianDivergence F) 2 (NlsGge.Ramer.finiteStdGaussian V))
    {φ : V → ℝ} (hφ : ContDiff ℝ 1 φ) (Bφ Bφ' : ℝ)
    (hφb : ∀ x, ‖φ x‖ ≤ Bφ) (hφ'b : ∀ x, ‖fderiv ℝ φ x‖ ≤ Bφ') :
    Integrable (fun x => φ x * NlsGge.Ramer.finiteGaussianDivergence F x)
        (NlsGge.Ramer.finiteStdGaussian V) ∧
    Integrable (fun x => fderiv ℝ φ x (F x)) (NlsGge.Ramer.finiteStdGaussian V) ∧
    ∫ x, φ x * NlsGge.Ramer.finiteGaussianDivergence F x ∂(NlsGge.Ramer.finiteStdGaussian V) =
      ∫ x, fderiv ℝ φ x (F x) ∂(NlsGge.Ramer.finiteStdGaussian V) := by
  set γ := NlsGge.Ramer.finiteStdGaussian V with hγ
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hFdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hFc : Continuous F := hF.continuous
  have hFi : Integrable F γ := hFL.integrable (by norm_num)
  have hδi : Integrable (NlsGge.Ramer.finiteGaussianDivergence F) γ := hδL.integrable (by norm_num)
  have hFn : Integrable (fun x => ‖F x‖) γ := hFi.norm
  have hδc : Continuous (NlsGge.Ramer.finiteGaussianDivergence F) :=
    NlsGge.Ramer.continuous_finiteGaussianDivergence hF1
  have hφc : Continuous φ := hφ.continuous
  have hφ'c : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hBφ : 0 ≤ Bφ := (norm_nonneg _).trans (hφb 0)
  have hBφ' : 0 ≤ Bφ' := (norm_nonneg _).trans (hφ'b 0)
  obtain ⟨M, hM0, hM⟩ := NlsGge.Ramer.exists_norm_fderiv_cutR_le (V := V)
  -- integrability of the two target integrands
  have hI1 : Integrable (fun x => φ x * NlsGge.Ramer.finiteGaussianDivergence F x) γ := by
    refine Integrable.mono' (hδi.norm.const_mul Bφ) (hφc.mul hδc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖φ x * NlsGge.Ramer.finiteGaussianDivergence F x‖ ≤
      Bφ * ‖NlsGge.Ramer.finiteGaussianDivergence F x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hφb x) (norm_nonneg _)
  have hI2 : Integrable (fun x => fderiv ℝ φ x (F x)) γ := by
    refine Integrable.mono' (hFn.const_mul Bφ') (hφ'c.clm_apply hFc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖fderiv ℝ φ x (F x)‖ ≤ Bφ' * ‖F x‖
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hφ'b x) (norm_nonneg _))
  -- cutoff facts
  have hcutC : ∀ n : ℕ, ContDiff ℝ 1 (r021Cut F n) := fun n =>
    (NlsGge.Ramer.contDiff_cutR (V := V) _ 1).smul hF1
  have hcutc : ∀ n : ℕ, HasCompactSupport (r021Cut F n) := fun n =>
    (NlsGge.Ramer.hasCompactSupport_cutR (V := V) (by positivity : (0 : ℝ) < (n : ℝ) + 1)).smul_right
  have hgr : ∀ n : ℕ, ∃ C : ℝ, (∀ v, ‖r021Cut F n v‖ ≤ C * (1 + ‖v‖) ^ (0 : ℕ)) ∧
      (∀ v, ‖fderiv ℝ (r021Cut F n) v‖ ≤ C * (1 + ‖v‖) ^ (0 : ℕ)) :=
    fun n => r021_growth_of_compact (hcutC n) (hcutc n)
  -- the integration by parts identity for each cutoff (production growth version)
  have hEq : ∀ n : ℕ, ∫ x, φ x * NlsGge.Ramer.finiteGaussianDivergence (r021Cut F n) x ∂γ =
      ∫ x, fderiv ℝ φ x (r021Cut F n x) ∂γ := by
    intro n
    obtain ⟨C, hC1, hC2⟩ := hgr n
    exact (NlsGge.Ramer.integral_mul_finiteGaussianDivergence_of_growth (hcutC n) C 0 hC1 hC2
      hφ Bφ Bφ' hφb hφ'b).2.2
  -- product rule for the cutoff divergence
  have hdiv : ∀ n : ℕ, ∀ x, NlsGge.Ramer.finiteGaussianDivergence (r021Cut F n) x =
      NlsGge.Ramer.cutR (V := V) ((n : ℝ) + 1) x * NlsGge.Ramer.finiteGaussianDivergence F x -
        fderiv ℝ (NlsGge.Ramer.cutR (V := V) ((n : ℝ) + 1)) x (F x) := by
    intro n x
    exact NlsGge.Ramer.finiteGaussianDivergence_smul (NlsGge.Ramer.cutR (V := V) ((n : ℝ) + 1)) F x
      ((NlsGge.Ramer.contDiff_cutR (V := V) _ 1).differentiable (by simp) x) (hFdiff x)
  have hdivb : ∀ n : ℕ, ∀ x, ‖NlsGge.Ramer.finiteGaussianDivergence (r021Cut F n) x‖ ≤
      ‖NlsGge.Ramer.finiteGaussianDivergence F x‖ + M * ‖F x‖ := by
    intro n x
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have h1 : ‖NlsGge.Ramer.cutR (V := V) ((n : ℝ) + 1) x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (NlsGge.Ramer.cutR_nonneg _ _)]
      exact NlsGge.Ramer.cutR_le_one _ _
    have h2 : ‖fderiv ℝ (NlsGge.Ramer.cutR (V := V) ((n : ℝ) + 1)) x (F x)‖ ≤ M * ‖F x‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hM _ hn1 x) (norm_nonneg _))
    rw [hdiv n x]
    calc ‖NlsGge.Ramer.cutR (V := V) ((n : ℝ) + 1) x *
          NlsGge.Ramer.finiteGaussianDivergence F x -
          fderiv ℝ (NlsGge.Ramer.cutR (V := V) ((n : ℝ) + 1)) x (F x)‖
        ≤ ‖NlsGge.Ramer.cutR (V := V) ((n : ℝ) + 1) x *
          NlsGge.Ramer.finiteGaussianDivergence F x‖ +
          ‖fderiv ℝ (NlsGge.Ramer.cutR (V := V) ((n : ℝ) + 1)) x (F x)‖ := norm_sub_le _ _
      _ ≤ ‖NlsGge.Ramer.finiteGaussianDivergence F x‖ + M * ‖F x‖ := by
          rw [norm_mul]
          exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) h1) h2
  -- pointwise eventual agreement in the cutoff index
  have hev : ∀ x : V, ∃ N : ℕ, ∀ n ≥ N, ‖x‖ < (n : ℝ) + 1 := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine ⟨N, fun n hn => ?_⟩
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hδlim : ∀ x : V, ∀ᶠ n in atTop,
      NlsGge.Ramer.finiteGaussianDivergence (r021Cut F n) x =
        NlsGge.Ramer.finiteGaussianDivergence F x := by
    intro x
    obtain ⟨N, hN⟩ := hev x
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    exact NlsGge.Ramer.finiteGaussianDivergence_cutR_smul
      (by positivity : (0 : ℝ) < (n : ℝ) + 1) F (hN n hn)
  have hFlim : ∀ x : V, ∀ᶠ n in atTop, r021Cut F n x = F x := by
    intro x
    obtain ⟨N, hN⟩ := hev x
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    exact (NlsGge.Ramer.cutR_smul_eventuallyEq (by positivity : (0 : ℝ) < (n : ℝ) + 1) F
      (hN n hn)).eq_of_nhds
  -- the first limit: dominated convergence for `φ δF_n`
  have hT1 : Tendsto (fun n : ℕ => ∫ x, φ x * NlsGge.Ramer.finiteGaussianDivergence (r021Cut F n) x ∂γ)
      atTop (𝓝 (∫ x, φ x * NlsGge.Ramer.finiteGaussianDivergence F x ∂γ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => Bφ * (‖NlsGge.Ramer.finiteGaussianDivergence F x‖ + M * ‖F x‖))
      (fun n => ((hφc.mul (NlsGge.Ramer.continuous_finiteGaussianDivergence (hcutC n))).aestronglyMeasurable))
      ((hδi.norm.add (hFn.const_mul M)).const_mul Bφ)
      (fun n => Filter.Eventually.of_forall fun x => ?_)
      (ae_of_all _ fun x => ?_)
    · show ‖φ x * NlsGge.Ramer.finiteGaussianDivergence (r021Cut F n) x‖ ≤
        Bφ * (‖NlsGge.Ramer.finiteGaussianDivergence F x‖ + M * ‖F x‖)
      rw [norm_mul]
      exact mul_le_mul (hφb x) (hdivb n x) (norm_nonneg _) hBφ
    · refine Tendsto.congr' ?_ tendsto_const_nhds
      exact (hδlim x).mono fun n hn => by
        show φ x * NlsGge.Ramer.finiteGaussianDivergence F x =
          φ x * NlsGge.Ramer.finiteGaussianDivergence (r021Cut F n) x
        rw [hn]
  -- the second limit: dominated convergence for `Dφ(F_n)`
  have hT2 : Tendsto (fun n : ℕ => ∫ x, fderiv ℝ φ x (r021Cut F n x) ∂γ) atTop
      (𝓝 (∫ x, fderiv ℝ φ x (F x) ∂γ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => Bφ' * ‖F x‖)
      (fun n => (hφ'c.clm_apply ((hcutC n).continuous)).aestronglyMeasurable)
      (hFn.const_mul Bφ')
      (fun n => Filter.Eventually.of_forall fun x => ?_)
      (ae_of_all _ fun x => ?_)
    · show ‖fderiv ℝ φ x (r021Cut F n x)‖ ≤ Bφ' * ‖F x‖
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hφ'b x) (NlsGge.Ramer.norm_cutR_smul_le _ F x) (norm_nonneg _) hBφ')
    · refine Tendsto.congr' ?_ tendsto_const_nhds
      exact (hFlim x).mono fun n hn => by
        show fderiv ℝ φ x (F x) = fderiv ℝ φ x (r021Cut F n x)
        rw [hn]
  have hT2' : Tendsto (fun n : ℕ => ∫ x, φ x * NlsGge.Ramer.finiteGaussianDivergence (r021Cut F n) x ∂γ)
      atTop (𝓝 (∫ x, fderiv ℝ φ x (F x) ∂γ)) :=
    Tendsto.congr (fun n => (hEq n).symm) hT2
  exact ⟨hI1, hI2, tendsto_nhds_unique hT1 hT2'⟩

end
end NlsGge.ThirdConsultation.R
