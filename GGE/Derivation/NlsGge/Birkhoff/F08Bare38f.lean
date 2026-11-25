import NlsGge.Birkhoff.F08Bare38e

/-! # F08 (v2 `C:thm:bare`), file f: statements on `H^{m-1}`

Transfer of the sequence-space results to the law `γ_m^F` on `H^{m-1}` and the final statements
`F08_L1_38` (`C:eq:L1`), `F08_normalizer_38` and `F08_weak_38` (`C:eq:barelimits`), packaged as
`F08_bare38`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory ProbabilityTheory Filter Topology NlsGge.Measure NlsGge.Pilot
  NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38 NlsGge.SpectralFoundations
open scoped ENNReal BoundedContinuousFunction

theorem truncSobolev38_eq_proj (r : ℝ) (N : ℕ) :
    truncSobolev38 r N = weightedRealProjectionContinuous (sobolevModeWeight r) (symmetricModes N) := by
  funext x
  apply Subtype.ext
  funext n
  change (show WeightedHilbert (sobolevModeWeight r) from truncSobolev38 r N x) n =
    (show WeightedHilbert (sobolevModeWeight r)
      from weightedRealProjectionContinuous (sobolevModeWeight r) (symmetricModes N) x) n
  rw [truncSobolev38_apply, weightedRealProjection_apply]
  rfl

theorem continuous_truncSobolev38 (r : ℝ) (N : ℕ) : Continuous (truncSobolev38 r N) := by
  rw [truncSobolev38_eq_proj]
  exact (weightedRealProjectionContinuous (sobolevModeWeight r) (symmetricModes N)).continuous

/-- The bare weight on `H^{m-1}`: `u ↦ e^{-V_m(P_N u)}`. -/
def weightFN38 (m : ℕ) (β : ℕ → ℝ) (N : ℕ) (u : Hm1 m) : ℝ :=
  Real.exp (-(Vm38 m β (truncSobolev38 _ N u)))

/-- The limiting weight on `H^{m-1}`: `u ↦ e^{-V_m(u)}`. -/
def weightFInf38 (m : ℕ) (β : ℕ → ℝ) (u : Hm1 m) : ℝ :=
  Real.exp (-(Vm38 m β u))

theorem continuous_Vm38' (m : ℕ) (β : ℕ → ℝ) : Continuous (Vm38 m β) :=
  continuous_vSobolev38 m β

theorem measurable_weightFN38 (m : ℕ) (β : ℕ → ℝ) (N : ℕ) : Measurable (weightFN38 m β N) :=
  Real.measurable_exp.comp ((continuous_Vm38' m β).comp (continuous_truncSobolev38 _ N)).measurable.neg

theorem measurable_weightFInf38 (m : ℕ) (β : ℕ → ℝ) : Measurable (weightFInf38 m β) :=
  Real.measurable_exp.comp (continuous_Vm38' m β).measurable.neg

section Transfer

variable {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

include hm hβ in
theorem ae_weightN_eq38 (N : ℕ) :
    weightN38 m β N =ᵐ[gammaM38 m β] fun ω => weightFN38 m β N (gaussianRealization38 m ω) := by
  filter_upwards [ae_PN_eq_trunc38 hm hβ] with ω hω
  simp only [weightN38, weightFN38, hω N]
  rfl

include hm hβ in
theorem integral_gammaF38 (g : Hm1 m → ℝ) (hg : Measurable g) :
    ∫ u, g u ∂(gammaFM38 m β) = ∫ ω, g (gaussianRealization38 m ω) ∂(gammaM38 m β) := by
  rw [gammaFM38_eq_realization m β]
  exact integral_map measurable_gaussianRealization38.aemeasurable hg.aestronglyMeasurable

include hm hβ in
theorem integrable_gammaF_iff38 (g : Hm1 m → ℝ) (hg : Measurable g) :
    Integrable g (gammaFM38 m β) ↔
      Integrable (fun ω => g (gaussianRealization38 m ω)) (gammaM38 m β) := by
  rw [gammaFM38_eq_realization m β]
  exact integrable_map_measure hg.aestronglyMeasurable measurable_gaussianRealization38.aemeasurable

end Transfer

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {m : ℕ} {β : ℕ → ℝ}
  (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

include O hm hβ in
/-- **`C:eq:L1` (v2 `C:thm:bare`).**  If `U ~ γ_m^F`, then `e^{-V_m(P_N U)}` and `e^{-V_m(U)}` are
integrable and `e^{-V_m(P_N U)} → e^{-V_m(U)}` in `L¹(γ_m^F)`; here `P_N = truncSobolev38 _ N` is the
Fourier projection onto `|n| ≤ N` in `H^{m-1}`. -/
theorem F08_L1_38 :
    (∀ N : ℕ, Integrable (fun u : Hm1 m => Real.exp (-(Vm38 m β (truncSobolev38 _ N u))))
      (gammaFM38 m β)) ∧
    Integrable (fun u : Hm1 m => Real.exp (-(Vm38 m β u))) (gammaFM38 m β) ∧
    Tendsto (fun N : ℕ => ∫ u, |Real.exp (-(Vm38 m β (truncSobolev38 _ N u))) -
        Real.exp (-(Vm38 m β u))| ∂(gammaFM38 m β)) atTop (𝓝 0) := by
  refine ⟨fun N => ?_, ?_, ?_⟩
  · exact (integrable_gammaF_iff38 hm hβ _ (measurable_weightFN38 m β N)).2
      ((integrable_weightN38 hm hβ N).congr (ae_weightN_eq38 hm hβ N))
  · exact (integrable_gammaF_iff38 hm hβ _ (measurable_weightFInf38 m β)).2
      (integrable_weightInf38 B O hm hβ)
  · obtain ⟨-, hL1⟩ := F08_weights_L1_38 B O hm hβ
    refine hL1.congr fun N => ?_
    have hmeas : Measurable (fun u : Hm1 m => |weightFN38 m β N u - weightFInf38 m β u|) :=
      ((measurable_weightFN38 m β N).sub (measurable_weightFInf38 m β)).abs
    have := integral_gammaF38 hm hβ _ hmeas
    refine Eq.trans ?_ this.symm
    refine integral_congr_ae ?_
    filter_upwards [ae_weightN_eq38 hm hβ N] with ω hω
    simp only [hω]
    rfl

include O hm hβ in
/-- **`C:eq:barelimits`, second clause.**  `𝒵_{m,N} / ∏_{|n|≤N} (π/a_{m,n}) → Z_m`. -/
theorem F08_normalizer_38 :
    Tendsto (fun N : ℕ => ZcalBare38 m β N /
      ∏ n ∈ Finset.Icc (-(N : ℤ)) N, (Real.pi / finiteHierarchyRate38 m β n)) atTop
      (𝓝 (ZM38 B m β)) := by
  have hprod : ∀ N : ℕ, ∏ n ∈ Finset.Icc (-(N : ℤ)) N,
      (Real.pi / finiteHierarchyRate38 m β n) = gaussConst38 m β N := by
    intro N
    unfold gaussConst38 windowRate38
    rw [← Finset.prod_image (f := fun n : ℤ => Real.pi / finiteHierarchyRate38 m β n)
      (s := Finset.univ) (g := modeIndex N) (fun a _ b _ h => modeIndex_injective N h)]
    congr 1
    ext n
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hn
      exact modeIndex_covers N n hn.1 hn.2
    · rintro ⟨i, rfl⟩
      exact modeIndex_bounds N i
  simp_rw [hprod]
  refine (F08_normalizer_gauss_tendsto38 B O hm hβ).congr fun N => ?_
  exact (ZcalBare_rel38 hm hβ N).symm

include hm hβ in
/-- `ν_{m,N}` as a probability measure on `H^{m-1}`. -/
def nuBarePM38 (N : ℕ) : ProbabilityMeasure (Hm1 m) :=
  ⟨nuBare38 m β N, isProbabilityMeasure_nuBare38 hm hβ N⟩

include hm hβ in
/-- `μ_m` as a probability measure on `H^{m-1}`. -/
def muPM38 : ProbabilityMeasure (Hm1 m) :=
  ⟨muM38 B m β, isProbabilityMeasure_muM38 B hm hβ⟩

include O hm hβ in
/-- **`C:eq:barelimits`, first clause.**  `ν_{m,N} ⇀ μ_m` on `H^{m-1}`, as convergence of
probability measures (weak topology). -/
theorem F08_weak_38 :
    Tendsto (fun N : ℕ => nuBarePM38 hm hβ N) atTop (𝓝 (muPM38 B hm hβ)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro F
  exact F08_weak_integral38 B O hm hβ F

end BirkhoffInput38

end NlsGge.Birkhoff

end
