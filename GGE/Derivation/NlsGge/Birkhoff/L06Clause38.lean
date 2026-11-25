import NlsGge.Birkhoff.F08Bare38h
set_option autoImplicit false
noncomputable section
namespace NlsGge.Birkhoff
open MeasureTheory ProbabilityTheory Filter Topology NlsGge.Measure NlsGge.Pilot
  NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38 NlsGge.SpectralFoundations NlsGge.AblowitzLadik
open scoped ENNReal BoundedContinuousFunction

/-- **L06.08(a), unconditional** (review REVIEW_F08 finding F1). The `m = 2` Fourier-truncated bare
Gibbs measures converge to `ρ₂ = alQ4Rho38` on `H^s` for every `s < 3/2`, and the relative normalizers
converge to `alQ4Z2_38`. No Birkhoff input: dominated convergence, since `V₂ ≥ 0`. -/
theorem L06_08a_free38 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) {s : ℝ}
    (hs : s < 3 / 2) (φ : SobolevHilbert s →ᵇ ℝ) :
    Tendsto (fun N : ℕ => ∫ u, φ u ∂(nuBareS38 2 (alQ4Beta38 β₀ β₁ β₂) N s)) atTop
      (𝓝 (∫ u, φ u ∂(alQ4Rho38 s β₀ β₁ β₂))) ∧
    Tendsto (fun N : ℕ => ZcalBare38 2 (alQ4Beta38 β₀ β₁ β₂) N /
      ∏ n ∈ Finset.Icc (-(N : ℤ)) N,
        (Real.pi / finiteHierarchyRate38 2 (alQ4Beta38 β₀ β₁ β₂) n)) atTop
      (𝓝 (alQ4Z2_38 β₀ β₁ β₂)) := by
  set β := alQ4Beta38 β₀ β₁ β₂ with hβdef
  have hβ := hβ_alQ4Beta38 h0 h1 h2
  have hm : 2 ≤ 2 := le_rfl
  have hVnn : ∀ u : Hm1 2, 0 ≤ Vm38 2 β u := fun u => by
    rw [Vm2_eq_alV2_reSob38]; exact alV2_nonneg38 h1.le h2.le _
  have hw1 : ∀ N ω, ‖weightN38 2 β N ω‖ ≤ 1 := fun N ω => by
    rw [Real.norm_of_nonneg (weightN38_pos 2 β N ω).le]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (hVnn (PN38 2 N ω)))
  have hae := ae_summable_sob38 h0 h1 h2 s hs
  have hφm : Measurable (fun u : SobolevHilbert s => φ u) := φ.continuous.measurable
  have hconvw := F08_ae_tendsto38 (m := 2) (β := β) hm hβ
  -- denominators
  have hden : Tendsto (fun N => ∫ ω, weightN38 2 β N ω ∂(gammaM38 2 β)) atTop
      (𝓝 (∫ ω, weightInf38 2 β ω ∂(gammaM38 2 β))) :=
    tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun N => (measurable_weightN38 2 β N).aestronglyMeasurable) (integrable_const _)
      (fun N => Eventually.of_forall (hw1 N)) hconvw
  have hVae : ∀ᵐ z ∂(gammaM38 2 β), weightInf38 2 β z = Real.exp (-alQ4V2Seq38 β₁ β₂ z) := by
    filter_upwards [ae_summable38 (m := 2) (β := β) hm (fun j hj => (hβ j hj).le)
        (hβ 0 (Nat.zero_le _)) (hβ 2 le_rfl)] with z hz
    have hz' : Summable (fun n : ℤ => sobolevModeWeight ((2 - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2) := hz
    have := Vm2_eq_alV2_reSob38 β₀ β₁ β₂ (gaussianRealization38 2 z)
    change Real.exp (-(Vm38 2 β (gaussianRealization38 2 z))) = _
    rw [this]
    unfold alQ4V2Seq38 gaussianRealization38
    rw [reSob38_realization _ _ z hz']
  have hZ : ∫ ω, weightInf38 2 β ω ∂(gammaM38 2 β) = alQ4Z2_38 β₀ β₁ β₂ := by
    unfold alQ4Z2_38
    exact integral_congr_ae hVae
  have hZpos := alQ4Z2_pos38 h0 h1.le h2
  refine ⟨?_, ?_⟩
  · set Gs : ℕ → (ℤ → ℂ) → ℝ := fun N ω => φ (planeElement38 s N (NlsGge.Ramer.windowProj N ω)) with hGs
    have hconvG : ∀ᵐ ω ∂(gammaM38 2 β), Tendsto (fun N : ℕ => Gs N ω) atTop
        (𝓝 (φ (seqRealization38 (sobolevModeWeight s) ω))) := by
      filter_upwards [hae] with ω hω
      exact (φ.continuous.tendsto _).comp (tendsto_planeElement38 s ω hω)
    have hnum : Tendsto (fun N => ∫ ω, Gs N ω * weightN38 2 β N ω ∂(gammaM38 2 β)) atTop
        (𝓝 (∫ ω, φ (seqRealization38 (sobolevModeWeight s) ω) * weightInf38 2 β ω ∂(gammaM38 2 β))) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
        (fun N => ?_) (integrable_const _) (fun N => ?_) ?_
      · exact ((hφm.comp ((measurable_finiteElement38 _ _).comp
          (NlsGge.Ramer.measurable_windowProj N))).mul (measurable_weightN38 2 β N)).aestronglyMeasurable
      · refine Eventually.of_forall fun ω => ?_
        rw [norm_mul]
        calc ‖Gs N ω‖ * ‖weightN38 2 β N ω‖ ≤ ‖φ‖ * 1 :=
              mul_le_mul (by simpa using φ.norm_coe_le_norm _) (hw1 N ω) (norm_nonneg _) (norm_nonneg _)
          _ = ‖φ‖ := mul_one _
      · filter_upwards [hconvG, hconvw] with ω h1 h2
        exact h1.mul h2
    have hlim : ∫ u, φ u ∂(alQ4Rho38 s β₀ β₁ β₂) =
        (∫ ω, φ (seqRealization38 (sobolevModeWeight s) ω) * weightInf38 2 β ω ∂(gammaM38 2 β)) /
          alQ4Z2_38 β₀ β₁ β₂ := by
      have hdm : Measurable (fun z : ℤ → ℂ => ENNReal.ofReal (Real.exp (-alQ4V2Seq38 β₁ β₂ z))) :=
        (Real.measurable_exp.comp (measurable_alQ4V2Seq38 β₁ β₂).neg).ennreal_ofReal
      unfold alQ4Rho38
      rw [integral_smul_measure, integral_map (measurable_seqRealization38 _).aemeasurable
        hφm.aestronglyMeasurable, integral_withDensity_eq_integral_toReal_smul hdm
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
        ENNReal.toReal_ofReal (inv_nonneg.2 hZpos.le), smul_eq_mul, div_eq_inv_mul]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hVae] with z hz
      rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, hz, smul_eq_mul, mul_comm]
    rw [hlim, ← hZ]
    refine (hnum.div hden (by rw [hZ]; exact hZpos.ne')).congr fun N => ?_
    rw [integral_nuBareS38 hm hβ N s _ hφm]
    rfl
  · have hprod : ∀ N : ℕ, ∏ n ∈ Finset.Icc (-(N : ℤ)) N,
        (Real.pi / finiteHierarchyRate38 2 β n) = gaussConst38 2 β N := by
      intro N
      unfold gaussConst38 windowRate38
      rw [← Finset.prod_image (f := fun n : ℤ => Real.pi / finiteHierarchyRate38 2 β n)
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
    rw [← hZ]
    exact hden.congr fun N => (ZcalBare_rel38 hm hβ N).symm
end NlsGge.Birkhoff
