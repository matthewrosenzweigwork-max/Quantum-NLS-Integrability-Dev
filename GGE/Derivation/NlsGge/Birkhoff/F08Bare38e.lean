import NlsGge.Birkhoff.F08Bare38d

/-! # F08 (v2 `C:thm:bare`), file e: uniform integrability, `L¹` convergence, normalizers

F08.04 (uniform integrability of the dominated weights, including the finitely many small
cutoffs), F08.05 (almost-sure convergence of the weights from `P_N U → U` and continuity of `V_m`),
F08.06 (`L¹`, normalizer and test-function convergence).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory ProbabilityTheory Filter Topology NlsGge.Measure NlsGge.Pilot
  NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38 NlsGge.SpectralFoundations
open scoped ENNReal BoundedContinuousFunction

section AE

variable {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

include hm hβ in
/-- **F08.05.**  `P_N U → U` almost surely in `H^{m-1}` and `V_m` is continuous, so
`e^{-V_m(P_N U)} → e^{-V_m(U)}` almost surely (`B` free). -/
theorem F08_ae_tendsto38 : ∀ᵐ ω ∂(gammaM38 m β),
    Tendsto (fun N => weightN38 m β N ω) atTop (𝓝 (weightInf38 m β ω)) := by
  filter_upwards [ae_PN_eq_trunc38 hm hβ] with ω hω
  have h1 : Tendsto (fun N => PN38 m N ω) atTop (𝓝 (gaussianRealization38 m ω)) := by
    simp_rw [hω]
    exact tendsto_truncSobolev38 _ _
  exact ((Real.continuous_exp.comp (continuous_vSobolev38 m β).neg).tendsto _).comp h1

include hm hβ in
/-- `P_N U → U` almost surely in `H^{m-1}` (sequence-space form). -/
theorem F08_ae_PN_tendsto38 : ∀ᵐ ω ∂(gammaM38 m β),
    Tendsto (fun N => PN38 m N ω) atTop (𝓝 (gaussianRealization38 m ω)) := by
  filter_upwards [ae_PN_eq_trunc38 hm hβ] with ω hω
  simp_rw [hω]
  exact tendsto_truncSobolev38 _ _

end AE

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {m : ℕ} {β : ℕ → ℝ}
  (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

include O hm hβ in
/-- `Z_m = ∫ e^{-V_m(U)} dγ_m` on the Gaussian sequence space (F05). -/
theorem ZM38_eq_integral_weightInf38 :
    ZM38 B m β = ∫ ω, weightInf38 m β ω ∂(gammaM38 m β) := by
  obtain ⟨-, -, hI, -⟩ := F05_cor_identity38 B O hm hβ
  rw [← hI, gammaFM38_eq_realization m β]
  have hm' : Measurable (fun u : Hm1 m => Real.exp (-Vm38 m β u)) :=
    Real.measurable_exp.comp (continuous_Vm38 (m := m) (β := β) hm hβ).neg.measurable
  exact integral_map measurable_gaussianRealization38.aemeasurable hm'.aestronglyMeasurable

include O hm hβ in
theorem integrable_weightInf38 : Integrable (weightInf38 m β) (gammaM38 m β) := by
  obtain ⟨-, hint, -⟩ := F05_cor_identity38 B O hm hβ
  rw [gammaFM38_eq_realization m β] at hint
  exact (integrable_map_measure hint.aestronglyMeasurable
    measurable_gaussianRealization38.aemeasurable).1 hint

include O hm hβ in
/-- **F08.04 + F08.06 (`C:eq:L1`), sequence-space form.**  The bare weights `e^{-V_m(P_N U)}` are
uniformly integrable (all `N`, including the finitely many small ones) and converge in `L¹` to
`e^{-V_m(U)}`. -/
theorem F08_weights_L1_38 :
    UnifIntegrable (weightN38 m β) 1 (gammaM38 m β) ∧
      Tendsto (fun N => ∫ ω, |weightN38 m β N ω - weightInf38 m β ω| ∂(gammaM38 m β)) atTop
        (𝓝 0) := by
  have hb0 : 0 < β (m - 1) := hβ (m - 1) (by omega)
  set δ : ℝ := β (m - 1) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < β (m - 1) := by rw [hδ]; linarith
  obtain ⟨N₀, -, hdom⟩ := F08_domination38 B O hm hβ hδ0 hδ1
  refine tendsto_L1_martingale_dominated38 NlsGge.Ramer.windowSigma
    NlsGge.Ramer.windowSigma_le_pi (termG38 m β δ) (integrable_termG38 B O hm hβ hδ0 hδ1)
    (Real.exp δ) (Real.exp_pos _).le N₀ (integrable_weightN38 hm hβ)
    (integrable_weightInf38 B O hm hβ) (fun N hN => ?_) (F08_ae_tendsto38 hm hβ) |> fun h => h
  filter_upwards [hdom N hN] with ω hω
  rw [Real.norm_of_nonneg (weightN38_pos m β N ω).le]
  calc weightN38 m β N ω ≤ Real.exp δ * (gammaM38 m β)[termG38 m β δ | NlsGge.Ramer.windowSigma N] ω := hω
    _ ≤ Real.exp δ * ‖(gammaM38 m β)[termG38 m β δ | NlsGge.Ramer.windowSigma N] ω‖ :=
        mul_le_mul_of_nonneg_left (Real.le_norm_self _) (Real.exp_pos _).le

include O hm hβ in
/-- Normalizer convergence in Gaussian form: `E[e^{-V_m(P_N U)}] → Z_m` (`C:eq:L1` integrated). -/
theorem F08_normalizer_gauss_tendsto38 :
    Tendsto (fun N => ∫ ω, weightN38 m β N ω ∂(gammaM38 m β)) atTop (𝓝 (ZM38 B m β)) := by
  obtain ⟨-, hL1⟩ := F08_weights_L1_38 B O hm hβ
  rw [ZM38_eq_integral_weightInf38 B O hm hβ]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hL1
  rw [← integral_sub (integrable_weightN38 hm hβ N) (integrable_weightInf38 B O hm hβ)]
  calc ‖∫ ω, (weightN38 m β N ω - weightInf38 m β ω) ∂(gammaM38 m β)‖
      ≤ ∫ ω, ‖weightN38 m β N ω - weightInf38 m β ω‖ ∂(gammaM38 m β) :=
        norm_integral_le_integral_norm _
    _ = _ := by simp only [Real.norm_eq_abs]

include O hm hβ in
/-- **F08.06, tests.**  For uniformly bounded measurable tests `G_N → G` a.e., the normalized
expectations `E[G_N e^{-V_m(P_N U)}] / E[e^{-V_m(P_N U)}]` converge to `E[G e^{-V_m(U)}] / Z_m`. -/
theorem F08_tests_tendsto38 {Gs : ℕ → (ℤ → ℂ) → ℝ} {G : (ℤ → ℂ) → ℝ} {C : ℝ}
    (hGm : ∀ N, Measurable (Gs N)) (hGb : ∀ N ω, ‖Gs N ω‖ ≤ C)
    (hconv : ∀ᵐ ω ∂(gammaM38 m β), Tendsto (fun N => Gs N ω) atTop (𝓝 (G ω))) :
    Tendsto (fun N => (∫ ω, Gs N ω * weightN38 m β N ω ∂(gammaM38 m β)) /
        ∫ ω, weightN38 m β N ω ∂(gammaM38 m β)) atTop
      (𝓝 ((∫ ω, G ω * weightInf38 m β ω ∂(gammaM38 m β)) / ZM38 B m β)) := by
  obtain ⟨-, hL1⟩ := F08_weights_L1_38 B O hm hβ
  have hnum := tendsto_integral_mul_L1_38 (integrable_weightN38 hm hβ)
    (integrable_weightInf38 B O hm hβ) hL1 (fun N => (hGm N).aestronglyMeasurable)
    (fun N => Eventually.of_forall (hGb N)) hconv
  exact hnum.div (F08_normalizer_gauss_tendsto38 B O hm hβ) (ZM38_pos_le_one B hm hβ).1.ne'

include O hm hβ in
/-- `∫ F dμ_m = E[F(U) e^{-V_m(U)}] / Z_m` (F05 identity `dμ_m = Z_m⁻¹ e^{-V_m} dγ_m^F`). -/
theorem integral_muM38_eq (F : Hm1 m → ℝ) (hF : Measurable F) :
    ∫ u, F u ∂(muM38 B m β) =
      (∫ ω, F (gaussianRealization38 m ω) * weightInf38 m β ω ∂(gammaM38 m β)) / ZM38 B m β := by
  obtain ⟨hmu, -, -, hZ, -⟩ := F05_cor_identity38 B O hm hβ
  have hdens : Measurable (fun u : Hm1 m =>
      ENNReal.ofReal ((ZM38 B m β)⁻¹ * Real.exp (-Vm38 m β u))) :=
    (measurable_const.mul (Real.measurable_exp.comp
      (continuous_Vm38 (m := m) (β := β) hm hβ).neg.measurable)).ennreal_ofReal
  rw [hmu, integral_withDensity_eq_integral_toReal_smul hdens
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), gammaFM38_eq_realization m β]
  have h1 : ∀ u : Hm1 m, (ENNReal.ofReal ((ZM38 B m β)⁻¹ * Real.exp (-Vm38 m β u))).toReal •
      F u = (ZM38 B m β)⁻¹ * (F u * Real.exp (-Vm38 m β u)) := by
    intro u
    rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 hZ.1.le) (Real.exp_pos _).le), smul_eq_mul]
    ring
  simp_rw [h1]
  rw [integral_const_mul]
  have hm' : Measurable (fun u : Hm1 m => F u * Real.exp (-Vm38 m β u)) :=
    hF.mul (Real.measurable_exp.comp (continuous_Vm38 (m := m) (β := β) hm hβ).neg.measurable)
  rw [integral_map measurable_gaussianRealization38.aemeasurable hm'.aestronglyMeasurable]
  have := hZ.1.ne'
  unfold weightInf38
  field_simp
  rfl

include O hm hβ in
/-- **`C:eq:barelimits` (first clause), as convergence of integrals of bounded continuous tests.**
`ν_{m,N} ⇀ μ_m` on `H^{m-1}`. -/
theorem F08_weak_integral38 (F : Hm1 m →ᵇ ℝ) :
    Tendsto (fun N => ∫ u, F u ∂(nuBare38 m β N)) atTop (𝓝 (∫ u, F u ∂(muM38 B m β))) := by
  have hFm : Measurable (fun u : Hm1 m => F u) := F.continuous.measurable
  have h := F08_tests_tendsto38 B O hm hβ (Gs := fun N ω => F (PN38 m N ω))
    (G := fun ω => F (gaussianRealization38 m ω)) (C := ‖F‖)
    (fun N => hFm.comp (measurable_PN38 m N))
    (fun N ω => by simpa using F.norm_coe_le_norm (PN38 m N ω))
    ((F08_ae_PN_tendsto38 hm hβ).mono fun ω hω => (F.continuous.tendsto _).comp hω)
  rw [integral_muM38_eq B O hm hβ F hFm]
  refine h.congr fun N => ?_
  rw [integral_nuBare38 hm hβ N F hFm]

end BirkhoffInput38

end NlsGge.Birkhoff

end
