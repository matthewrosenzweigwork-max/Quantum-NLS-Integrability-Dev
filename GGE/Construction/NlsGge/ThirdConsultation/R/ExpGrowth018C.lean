import Mathlib
import NlsGge.Ramer.FiniteDivergenceGrowth
import NlsGge.Ramer.FiniteDivergenceL2
import NlsGge.ThirdConsultation.R.ExpGrowth018B

                                                                                                             
                                                                                                                        
                                                                    
                                                                                                                 
                                                                                                                
                                                                                                                     
set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Real
open scoped Topology RealInnerProductSpace ContDiff

namespace NlsGge.ThirdConsultation.R
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Exponential-growth Gaussian divergence identity** (general finite-dimensional carrier).
Integrability of `(δF)²`, `‖F‖²` and `tr(DF∘DF)` under the standard Gaussian, and the identity
`∫ (δF)² dγ = ∫ ‖F‖² dγ + ∫ tr(DF∘DF) dγ`. -/
theorem integral_sq_finiteGaussianDivergence_expGrowth {F : V → V} (hF : ContDiff ℝ 2 F)
    {C : ℝ} (hC : 0 < C) (hFg : ∀ x, ‖F x‖ ≤ C * Real.exp (C * ‖x‖))
    (hDg : ∀ x, ‖fderiv ℝ F x‖ ≤ C * Real.exp (C * ‖x‖)) :
    Integrable (fun x => (NlsGge.Ramer.finiteGaussianDivergence F x) ^ 2)
        (NlsGge.Ramer.finiteStdGaussian V) ∧
      Integrable (fun x => ‖F x‖ ^ 2) (NlsGge.Ramer.finiteStdGaussian V) ∧
      Integrable (fun x => NlsGge.Ramer.traceCLM V ((fderiv ℝ F x).comp (fderiv ℝ F x)))
        (NlsGge.Ramer.finiteStdGaussian V) ∧
      ∫ x, (NlsGge.Ramer.finiteGaussianDivergence F x) ^ 2 ∂(NlsGge.Ramer.finiteStdGaussian V) =
        ∫ x, ‖F x‖ ^ 2 ∂(NlsGge.Ramer.finiteStdGaussian V) +
          ∫ x, NlsGge.Ramer.traceCLM V ((fderiv ℝ F x).comp (fderiv ℝ F x))
            ∂(NlsGge.Ramer.finiteStdGaussian V) := by
  have hC0 : 0 ≤ C := hC.le
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hFdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hA : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  obtain ⟨M, hM0, hM⟩ := NlsGge.Ramer.exists_norm_fderiv_cutR_le (V := V)
  -- continuity of the three integrands
  have hcont_F : Continuous (fun x => ‖F x‖ ^ 2) := by
    have := hF.continuous
    fun_prop
  have hcont_δ : Continuous (fun x => (NlsGge.Ramer.finiteGaussianDivergence F x) ^ 2) :=
    (NlsGge.Ramer.continuous_finiteGaussianDivergence hF1).pow 2
  have hcont_T : Continuous (fun x => NlsGge.Ramer.traceCLM V ((fderiv ℝ F x).comp (fderiv ℝ F x))) :=
    (NlsGge.Ramer.traceCLM V).continuous.comp (hA.continuous.clm_comp hA.continuous)
  -- pointwise exponential bound for the divergence of `F`
  have hδF : ∀ x, |NlsGge.Ramer.finiteGaussianDivergence F x| ≤
      (C + (Module.finrank ℝ V : ℝ) * C) * ((1 + ‖x‖) * Real.exp (C * ‖x‖)) :=
    fun x => abs_finiteGaussianDivergence_le_exp hC0 hC0 x (hFg x) (hDg x)
  -- integrability of the three integrands for `F`
  have hI1 : Integrable (fun x => (NlsGge.Ramer.finiteGaussianDivergence F x) ^ 2)
      (NlsGge.Ramer.finiteStdGaussian V) :=
    integrable_of_norm_le_pow_mul_exp_finiteStd hcont_δ.aestronglyMeasurable
      ((C + (Module.finrank ℝ V : ℝ) * C) ^ 2) (2 * C) 2 (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        refine (sq_le_sq_mul_of_abs_le (hδF x)).trans (le_of_eq ?_)
        rw [mul_pow, sq_mul_exp_eq])
  have hI2 : Integrable (fun x => ‖F x‖ ^ 2) (NlsGge.Ramer.finiteStdGaussian V) :=
    integrable_of_norm_le_pow_mul_exp_finiteStd hcont_F.aestronglyMeasurable (C ^ 2) (2 * C) 0
      (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        refine (sq_le_sq_mul_of_le (norm_nonneg _) (hFg x)).trans (le_of_eq ?_)
        rw [sq_mul_exp_eq, pow_zero, one_mul])
  have hI3 : Integrable (fun x => NlsGge.Ramer.traceCLM V ((fderiv ℝ F x).comp (fderiv ℝ F x)))
      (NlsGge.Ramer.finiteStdGaussian V) :=
    integrable_of_norm_le_pow_mul_exp_finiteStd hcont_T.aestronglyMeasurable
      ((Module.finrank ℝ V : ℝ) * C ^ 2) (2 * C) 0 (fun x => by
        rw [Real.norm_eq_abs]
        refine (abs_traceCLM_comp_self_le_exp x (hDg x) hC0).trans (le_of_eq ?_)
        rw [pow_zero, one_mul]
        ring)
  -- cut-off sequence `G n = χ(·/(n+1)) F` (production `cutR`, radii `n+1 ≥ 1`)
  let Rn : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hRn0 : ∀ n, 0 < Rn n := fun n => by positivity
  have hRn1 : ∀ n, 1 ≤ Rn n := fun n => by simp [Rn]
  let G : ℕ → V → V := fun n y => NlsGge.Ramer.cutR (Rn n) y • F y
  have hG2 : ∀ n, ContDiff ℝ 2 (G n) := fun n =>
    (NlsGge.Ramer.contDiff_cutR (V := V) (Rn n) 2).smul hF
  have hGc : ∀ n, HasCompactSupport (G n) := fun n =>
    (NlsGge.Ramer.hasCompactSupport_cutR (hRn0 n)).smul_right
  have hG1 : ∀ n, ContDiff ℝ 1 (G n) := fun n => (hG2 n).of_le (by norm_num)
  have hGb : ∀ n x, ‖G n x‖ ≤ C * Real.exp (C * ‖x‖) := fun n x =>
    (NlsGge.Ramer.norm_cutR_smul_le _ F x).trans (hFg x)
  have hGDb : ∀ n x, ‖fderiv ℝ (G n) x‖ ≤ (C * (1 + M)) * Real.exp (C * ‖x‖) := by
    intro n x
    have h := NlsGge.Ramer.norm_fderiv_cutR_smul_le hFdiff (R := Rn n) (hM _ (hRn1 n)) x
    refine h.trans ?_
    calc ‖fderiv ℝ F x‖ + M * ‖F x‖ ≤ C * Real.exp (C * ‖x‖) + M * (C * Real.exp (C * ‖x‖)) :=
          add_le_add (hDg x) (mul_le_mul_of_nonneg_left (hFg x) hM0)
      _ = (C * (1 + M)) * Real.exp (C * ‖x‖) := by ring
  have hB0 : 0 ≤ C * (1 + M) := mul_nonneg hC0 (by linarith)
  have hGδb : ∀ n x, |NlsGge.Ramer.finiteGaussianDivergence (G n) x| ≤
      (C + (Module.finrank ℝ V : ℝ) * (C * (1 + M))) * ((1 + ‖x‖) * Real.exp (C * ‖x‖)) :=
    fun n x => abs_finiteGaussianDivergence_le_exp hC0 hB0 x (hGb n x) (hGDb n x)
  have hev : ∀ x : V, ∃ N : ℕ, ∀ n ≥ N, ‖x‖ < Rn n := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    exact ⟨N, fun n hn => by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      simp only [Rn]
      linarith⟩
  -- the three limits as `n → ∞`
  have hL : Tendsto (fun n => ∫ x, (NlsGge.Ramer.finiteGaussianDivergence (G n) x) ^ 2
      ∂(NlsGge.Ramer.finiteStdGaussian V)) atTop
      (𝓝 (∫ x, (NlsGge.Ramer.finiteGaussianDivergence F x) ^ 2
        ∂(NlsGge.Ramer.finiteStdGaussian V))) := by
    refine tendsto_integral_of_exp_bound_finiteStd (fun n => ?_)
      ((C + (Module.finrank ℝ V : ℝ) * (C * (1 + M))) ^ 2) (2 * C) 2 (fun n x => ?_) (fun x => ?_)
    · exact ((NlsGge.Ramer.continuous_finiteGaussianDivergence (hG1 n)).pow 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      refine (sq_le_sq_mul_of_abs_le (hGδb n x)).trans (le_of_eq ?_)
      rw [mul_pow, sq_mul_exp_eq]
    · obtain ⟨N, hN⟩ := hev x
      exact ⟨N, fun n hn => by
        rw [NlsGge.Ramer.finiteGaussianDivergence_cutR_smul (hRn0 n) F (hN n hn)]⟩
  have hR1 : Tendsto (fun n => ∫ x, ‖G n x‖ ^ 2 ∂(NlsGge.Ramer.finiteStdGaussian V)) atTop
      (𝓝 (∫ x, ‖F x‖ ^ 2 ∂(NlsGge.Ramer.finiteStdGaussian V))) := by
    refine tendsto_integral_of_exp_bound_finiteStd (fun n => ?_) (C ^ 2) (2 * C) 0
      (fun n x => ?_) (fun x => ?_)
    · exact (((hG2 n).continuous.norm).pow 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      refine (sq_le_sq_mul_of_le (norm_nonneg _) (hGb n x)).trans (le_of_eq ?_)
      rw [sq_mul_exp_eq, pow_zero, one_mul]
    · obtain ⟨N, hN⟩ := hev x
      refine ⟨N, fun n hn => ?_⟩
      show ‖NlsGge.Ramer.cutR (Rn n) x • F x‖ ^ 2 = _
      rw [NlsGge.Ramer.cutR_eq_one (hRn0 n) (hN n hn), one_smul]
  have hR2 : Tendsto (fun n => ∫ x, NlsGge.Ramer.traceCLM V
      ((fderiv ℝ (G n) x).comp (fderiv ℝ (G n) x)) ∂(NlsGge.Ramer.finiteStdGaussian V)) atTop
      (𝓝 (∫ x, NlsGge.Ramer.traceCLM V ((fderiv ℝ F x).comp (fderiv ℝ F x))
        ∂(NlsGge.Ramer.finiteStdGaussian V))) := by
    refine tendsto_integral_of_exp_bound_finiteStd (fun n => ?_)
      ((Module.finrank ℝ V : ℝ) * (C * (1 + M)) ^ 2) (2 * C) 0 (fun n x => ?_) (fun x => ?_)
    · have hAn : ContDiff ℝ 1 (fderiv ℝ (G n)) := (hG2 n).fderiv_right (m := 1) (by norm_num)
      exact ((NlsGge.Ramer.traceCLM V).continuous.comp
        (hAn.continuous.clm_comp hAn.continuous)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      refine (abs_traceCLM_comp_self_le_exp x (hGDb n x) hB0).trans (le_of_eq ?_)
      rw [pow_zero, one_mul]
      ring
    · obtain ⟨N, hN⟩ := hev x
      refine ⟨N, fun n hn => ?_⟩
      rw [show fderiv ℝ (G n) x = fderiv ℝ F x from
        NlsGge.Ramer.fderiv_cutR_smul_eq (hRn0 n) F (hN n hn)]
  -- the identity for each cut-off field (compact support), then pass to the limit
  have hEq : ∀ n, ∫ x, (NlsGge.Ramer.finiteGaussianDivergence (G n) x) ^ 2
      ∂(NlsGge.Ramer.finiteStdGaussian V) =
        ∫ x, ‖G n x‖ ^ 2 ∂(NlsGge.Ramer.finiteStdGaussian V) +
          ∫ x, NlsGge.Ramer.traceCLM V ((fderiv ℝ (G n) x).comp (fderiv ℝ (G n) x))
            ∂(NlsGge.Ramer.finiteStdGaussian V) :=
    fun n => NlsGge.Ramer.integral_sq_finiteGaussianDivergence (hG2 n) (hGc n)
  have hT : Tendsto (fun n => ∫ x, (NlsGge.Ramer.finiteGaussianDivergence (G n) x) ^ 2
      ∂(NlsGge.Ramer.finiteStdGaussian V)) atTop
      (𝓝 (∫ x, ‖F x‖ ^ 2 ∂(NlsGge.Ramer.finiteStdGaussian V) +
        ∫ x, NlsGge.Ramer.traceCLM V ((fderiv ℝ F x).comp (fderiv ℝ F x))
          ∂(NlsGge.Ramer.finiteStdGaussian V))) :=
    Tendsto.congr (fun n => (hEq n).symm) (hR1.add hR2)
  exact ⟨hI1, hI2, hI3, tendsto_nhds_unique hL hT⟩

end
end NlsGge.ThirdConsultation.R
