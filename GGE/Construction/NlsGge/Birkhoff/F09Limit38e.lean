import NlsGge.Birkhoff.F09Limit38d

/-! # NEW-F09, file 5: the unnormalized limit `F:eq:fullunnorm` (conditional on `B`, `O`)

Source: `paper/v2.tex` l.1774-1784. Conditional on `B : BirkhoffInput38` (E01) and
`O : OneSmoothingInput38 B` (E04), for `1/2 < s < 3/4`.

For `F : L² → ℝ` bounded and continuous on `𝓕⁻¹E_s` (`F ∘ physOfE38` continuous and bounded):

`∫_{E_s} F(𝓕⁻¹P_N x) f_N(x) dγ_W(x) → Z_W ∫ F dμ_W`.

Proof (v2): fix `R > 0` and apply W10 (`W10_38`) with the cutoff `χ_R`; by `unloc_sub_loc38` and
`tail_Es38` the unlocalized and localized integrals differ by at most `M C e^{-η R²}` uniformly in `N`
(NEW-F08); `∫ F χ_R dμ_W → ∫ F dμ_W` as `R → ∞` by bounded convergence under the probability `μ_W`
(`μ_W`-a.e. `u` lies in `𝓕⁻¹E_s`, where `χ_R(u) = 1` for large `R`); first `N → ∞`, then `R → ∞`
(`double_limit38`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer Filter Topology
open scoped ENNReal Real

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

include B O in
/-- Bounded convergence as the radius tends to infinity (v2 l.1779-1780). -/
theorem tendsto_integral_chiR38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ}
    (hχ : CutoffProfile38 χ) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y))) (M : ℝ)
    (hM : ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    Tendsto (fun R : ℝ => ∫ u, F u * chiR38 χ R u ∂(B.muW38 c.val)) atTop
      (𝓝 (∫ u, F u ∂(B.muW38 c.val))) := by
  have hprob := B.isProbabilityMeasure_muW38 lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_
    (integrable_const M) ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact B.aestronglyMeasurable_muW38 O c hs hs' (fun u => F u * chiR38 χ R u)
      (hF.mul (continuous_chiR38_physOfE38 c s hχ hR))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    filter_upwards [B.ae_mem_range_muW38 O c hs hs'] with u hu
    obtain ⟨y, rfl⟩ := hu
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have h2 := chiR38_mem_Icc hχ hR (physOfE38 c s y)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2.1]
    calc _ ≤ M * 1 := mul_le_mul (hM y) h2.2 h2.1 hM0
      _ = M := mul_one M
  · filter_upwards [B.ae_mem_range_muW38 O c hs hs'] with u hu
    obtain ⟨y, rfl⟩ := hu
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) y‖),
      eventually_gt_atTop (0 : ℝ)] with R hR hR0
    rw [chiR38_physOfE38, hχ.eq_one _ (div_nonneg (norm_nonneg _) hR0.le)
      ((div_le_one hR0).2 hR), mul_one]

include B O in
/-- **`F:eq:fullunnorm` (v2 l.1782-1783).** -/
theorem fullunnorm_Es38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (hFb : ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
        ∂(fullWeightedSequenceGaussian c s)) atTop
      (𝓝 (B.ZW38 c.val * ∫ u, F u ∂(B.muW38 c.val))) := by
  obtain ⟨χ, hχ⟩ := exists_cutoffProfile38
  obtain ⟨η, C, hη, hC, htail⟩ := tail_Es38 lower upper (coef_lower38 c) c.property.2.1
  obtain ⟨M, hM⟩ := hFb
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine double_limit38 _ (fun R N => ∫ x, locIntegrand38 c χ R F N x ∂(fullWeightedSequenceGaussian c s))
    (fun R => B.ZW38 c.val * ∫ u, F u * chiR38 χ R u ∂(B.muW38 c.val))
    (fun R => M * (C * Real.exp (-(η * R ^ 2)))) _ ?_ ?_ ?_ ?_
  · intro R hR
    exact (B.W10_38 O c hs hs' hχ hR).1 F hF ⟨M, hM⟩
  · intro R hR N
    refine (unloc_sub_loc38 c s hs hχ hR F hF M hM N).trans ?_
    exact mul_le_mul_of_nonneg_left (htail c s hs N R hR.le).2 hM0
  · have h1 : Tendsto (fun R : ℝ => η * R ^ 2) atTop atTop :=
      Tendsto.const_mul_atTop hη (tendsto_pow_atTop two_ne_zero)
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    simpa using (h2.const_mul C).const_mul M
  · exact (B.tendsto_integral_chiR38 O c hs hs' hχ F hF M hM).const_mul _

include B O in
/-- **`Z_N(W) → Z_W > 0` (v2 l.1783-1784, `F = 1`).** -/
theorem Z_tendsto_38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    Tendsto (fun N : ℕ => relativePartition38 c N) atTop (𝓝 (B.ZW38 c.val)) ∧ 0 < B.ZW38 c.val := by
  have hprob := B.isProbabilityMeasure_muW38 lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)
  have h := B.fullunnorm_Es38 O c hs hs' (fun _ => 1) continuous_const ⟨1, fun _ => by simp⟩
  simp only [one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  refine ⟨?_, (B.ZW38_pos_le_one lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)).1⟩
  refine h.congr fun N => ?_
  exact integral_fN38 c s hs N

end BirkhoffInput38

end NlsGge.Birkhoff
end
