import NlsGge.Ramer.General.RamerStep10G
import NlsGge.Ramer.General.CylindricalDensityConvergenceG
import NlsGge.Ramer.General.DivergenceIdentificationGlobalG
import NlsGge.Ramer.General.SpaceTransferG

/-!
# G4 / GE11: the general Ramer theorem over a `RamerSetting`

Adapted from `NlsGge/Ramer/RamerTheorem.lean` (v2 `eq:Ramercommon`, `eq:cylindricalcommon`).
The statements keep the old shape, translated by the G3 dictionary
(`FullWeightedHilbert c s ↦ S.E`, `ActualCM c ↦ S.H`, `inclE ↦ S.incl`,
`fullWeightSequenceGaussian c.val ↦ S.γ`, `fullWeightedSequenceGaussian c s ↦ S.γE`,
`fullWeightedSequenceRealization c s ↦ S.R`, `coordE c s ↦ S.coordE`,
`headPt c N ↦ S.headPt N`, `truncField c s K ↦ S.truncField K`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant NlsGge.Ramer

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- Any two divergences satisfying clauses 2 and 3 (clause 2 is only needed for `δ₁`) agree
`γ`-a.e. (Old: `v2_divergence_unique`.) -/
theorem v2_divergence_unique (K : S.E → S.H)
    (δ₁ δ₂ : (ℤ → ℂ) → ℝ)
    (h2 : ∀ x₀, ∃ r > 0, ∃ (G : S.E → S.H) (η : (ℤ → ℂ) → ℝ),
      Set.EqOn G K (ball x₀ r) ∧
      S.IsClosedDiv (fun z => G (S.R z)) η)
    (h3₁ : ∀ (x₀ : S.E) (r : ℝ) (G : S.E → S.H)
        (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (ball x₀ r) →
        S.IsClosedDiv (fun z => G (S.R z)) η →
        ∀ᵐ z ∂S.γ, S.R z ∈ ball x₀ r → δ₁ z = η z)
    (h3₂ : ∀ (x₀ : S.E) (r : ℝ) (G : S.E → S.H)
        (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (ball x₀ r) →
        S.IsClosedDiv (fun z => G (S.R z)) η →
        ∀ᵐ z ∂S.γ, S.R z ∈ ball x₀ r → δ₂ z = η z) :
    δ₁ =ᵐ[S.γ] δ₂ := by
  choose r hr G η hEq hCD using h2
  obtain ⟨T, hTc, hTcov⟩ := S.exists_countable_cover_balls r hr
  have hae : ∀ x ∈ T, ∀ᵐ z ∂S.γ, S.R z ∈ ball x (r x) → δ₁ z = δ₂ z := by
    intro x _
    filter_upwards [h3₁ x (r x) (G x) (η x) (hEq x) (hCD x),
      h3₂ x (r x) (G x) (η x) (hEq x) (hCD x)] with z h1 h2
    intro hz
    rw [h1 hz, h2 hz]
  have hall := (MeasureTheory.ae_ball_iff hTc).2 hae
  filter_upwards [hall] with z hz
  obtain ⟨y, hy, hzy⟩ := hTcov (S.R z)
  exact hz y hy hzy

/-- **Ramer's theorem (v2 `eq:Ramercommon`, `eq:cylindricalcommon`), `C²` form**, over a general
`RamerSetting`. (Old: `ramer_eq_Ramercommon_C2`.) -/
theorem ramer_general
    (T : S.E ≃ₜ S.E)
    (K K' : S.E → S.H)
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTs : ∀ y, T.symm y = y + S.incl (K' y))
    (hK : ContDiff ℝ 2 K) (hK' : ContDiff ℝ 2 K') :
    ∃ δK : (ℤ → ℂ) → ℝ,
      (∀ x₀ : S.E, ∃ r > 0,
        ∃ (G : S.E → S.H) (η : (ℤ → ℂ) → ℝ),
          Set.EqOn G K (ball x₀ r) ∧
          S.IsClosedDiv (fun z => G (S.R z)) η) ∧
      (∀ (x₀ : S.E) (r : ℝ) (G : S.E → S.H)
          (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (ball x₀ r) →
          S.IsClosedDiv (fun z => G (S.R z)) η →
          ∀ᵐ z ∂S.γ, S.R z ∈ ball x₀ r → δK z = η z) ∧
      let J : S.E → ℝ := fun x =>
        |det2 (S.hsDerivH K x)| *
          Real.exp (-(δK (S.coordE x)) - ‖K x‖ ^ 2 / 2)
      S.γE.map T.symm = S.γE.withDensity (fun x => ENNReal.ofReal (J x)) ∧
      (∀ x, 0 < J x) ∧
      Integrable J S.γE ∧
      ∫ x, J x ∂S.γE = 1 ∧
      TendstoInMeasure S.γ
        (fun N z => finiteRamerDensity (fun v => v + S.truncField K N v) (S.headPt N z))
        atTop (fun z => J (S.R z)) := by
  have hspec := Classical.choose_spec (S.divergence_identification K hK)
  have hdef : S.ramerDiv K = Classical.choose (S.divergence_identification K hK) := by
    unfold ramerDiv; rw [dif_pos hK]
  rw [← hdef] at hspec
  obtain ⟨hm, h2, h3, -, -⟩ := hspec
  refine ⟨S.ramerDiv K, h2, h3, ?_⟩
  intro J
  set γ := S.γE with hγ
  have hJeq : J = S.ramerJE K (S.ramerDiv K) := by
    funext x; rw [S.ramerJE_eq]
  have hJeq' : J = S.ramerJac K := by
    funext x; rw [S.ramerJac_eq]
  have hpos : ∀ x, 0 < J x := by
    intro x
    rw [hJeq]
    exact S.ramerJE_pos T K K' hT hTs (hK.of_le (by norm_num)) (hK'.of_le (by norm_num))
      _ x
  obtain ⟨Jt, hJtm, hJae, hmap⟩ := S.ramer_step10_global T K K' hK hK' hT hTs
  have hmap' : γ.map T.symm = γ.withDensity (fun x => ENNReal.ofReal (J x)) := by
    rw [hmap, hJeq']
    exact withDensity_congr_ae hJae
  have hprob : IsProbabilityMeasure γ := by
    rw [hγ]; infer_instance
  have hone : ∫⁻ x, ENNReal.ofReal (J x) ∂γ = 1 := by
    have h1 : (γ.map T.symm) Set.univ = 1 := by
      rw [Measure.map_apply T.symm.continuous.measurable MeasurableSet.univ]
      simp
    rw [hmap', withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    exact h1
  have hJam : AEStronglyMeasurable J γ := by
    rw [hJeq]
    exact S.aestronglyMeasurable_ramerJE K (hK.of_le (by norm_num)) _ hm
  have hint : Integrable J γ := by
    refine ⟨hJam, ?_⟩
    unfold HasFiniteIntegral
    have : ∫⁻ x, ‖J x‖ₑ ∂γ = 1 := by
      rw [← hone]
      refine lintegral_congr fun x => ?_
      rw [Real.enorm_of_nonneg (hpos x).le]
    rw [this]; exact ENNReal.one_lt_top
  refine ⟨hmap', hpos, hint, ?_, ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (hpos x).le) hJam,
      hone]
    simp
  · have hconv := S.tendstoInMeasure_cylindricalDensity K hK (S.ramerDiv K) h3
    refine TendstoInMeasure.congr (fun i => ae_eq_refl _) ?_ hconv
    filter_upwards [S.coordE_realization_ae] with z hz
    show S.ramerJ K (S.ramerDiv K) z = J (S.R z)
    simp only [J, ramerJ, hz]

/-- **Ramer's theorem, analytic form** (v2 `prop:gaussiancommon` hypotheses).
(Old: `ramer_eq_Ramercommon`.) -/
theorem ramer_general_analytic
    (T : S.E ≃ₜ S.E)
    (K K' : S.E → S.H)
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTs : ∀ y, T.symm y = y + S.incl (K' y))
    (hK : AnalyticOnNhd ℝ K Set.univ) (hK' : AnalyticOnNhd ℝ K' Set.univ) :
    ∃ δK : (ℤ → ℂ) → ℝ,
      (∀ x₀ : S.E, ∃ r > 0,
        ∃ (G : S.E → S.H) (η : (ℤ → ℂ) → ℝ),
          Set.EqOn G K (ball x₀ r) ∧
          S.IsClosedDiv (fun z => G (S.R z)) η) ∧
      (∀ (x₀ : S.E) (r : ℝ) (G : S.E → S.H)
          (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (ball x₀ r) →
          S.IsClosedDiv (fun z => G (S.R z)) η →
          ∀ᵐ z ∂S.γ, S.R z ∈ ball x₀ r → δK z = η z) ∧
      let J : S.E → ℝ := fun x =>
        |det2 (S.hsDerivH K x)| *
          Real.exp (-(δK (S.coordE x)) - ‖K x‖ ^ 2 / 2)
      S.γE.map T.symm = S.γE.withDensity (fun x => ENNReal.ofReal (J x)) ∧
      (∀ x, 0 < J x) ∧
      Integrable J S.γE ∧
      ∫ x, J x ∂S.γE = 1 ∧
      TendstoInMeasure S.γ
        (fun N z => finiteRamerDensity (fun v => v + S.truncField K N v) (S.headPt N z))
        atTop (fun z => J (S.R z)) :=
  S.ramer_general T K K' hT hTs hK.contDiff hK'.contDiff

end NlsGge.Ramer.General.RamerSetting
