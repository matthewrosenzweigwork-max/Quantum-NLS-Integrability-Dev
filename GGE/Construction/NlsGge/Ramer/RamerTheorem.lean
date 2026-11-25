import NlsGge.Ramer.RamerStep10
import NlsGge.Ramer.CylindricalDensityConvergence
import NlsGge.Ramer.DivergenceIdentificationGlobal
import NlsGge.Ramer.SpaceTransfer

/-!
# P7 / R10b: the final Ramer theorem (v2 `eq:Ramercommon`, `eq:cylindricalcommon`)
-/

open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

variable {lower upper : ℝ}

/-- Any two divergences satisfying clauses 2 and 3 (clause 2 is only needed for `δ₁`) agree
`γ`-a.e. -/
theorem v2_divergence_unique (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s → ActualCM c)
    (δ₁ δ₂ : (ℤ → ℂ) → ℝ)
    (h2 : ∀ x₀, ∃ r > 0, ∃ (G : FullWeightedHilbert c s → ActualCM c) (η : (ℤ → ℂ) → ℝ),
      Set.EqOn G K (ball x₀ r) ∧
      IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η)
    (h3₁ : ∀ (x₀ : FullWeightedHilbert c s) (r : ℝ) (G : FullWeightedHilbert c s → ActualCM c)
        (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (ball x₀ r) →
        IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η →
        ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
          NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball x₀ r → δ₁ z = η z)
    (h3₂ : ∀ (x₀ : FullWeightedHilbert c s) (r : ℝ) (G : FullWeightedHilbert c s → ActualCM c)
        (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (ball x₀ r) →
        IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η →
        ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
          NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball x₀ r → δ₂ z = η z) :
    δ₁ =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val] δ₂ := by
  choose r hr G η hEq hCD using h2
  obtain ⟨T, hTc, hTcov⟩ := exists_countable_cover_balls c s r hr
  have hae : ∀ x ∈ T, ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball x (r x) → δ₁ z = δ₂ z := by
    intro x _
    filter_upwards [h3₁ x (r x) (G x) (η x) (hEq x) (hCD x),
      h3₂ x (r x) (G x) (η x) (hEq x) (hCD x)] with z h1 h2
    intro hz
    rw [h1 hz, h2 hz]
  have hall := (MeasureTheory.ae_ball_iff hTc).2 hae
  filter_upwards [hall] with z hz
  obtain ⟨y, hy, hzy⟩ := hTcov (NlsGge.Measure.fullWeightedSequenceRealization c s z)
  exact hz y hy hzy

/-- **Ramer's theorem (v2 `eq:Ramercommon`, `eq:cylindricalcommon`), `C²` form.** -/
theorem ramer_eq_Ramercommon_C2 (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s)
    (T : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (K K' : FullWeightedHilbert c s → ActualCM c)
    (hT : ∀ x, T x = x + inclE c s hs (K x))
    (hTs : ∀ y, T.symm y = y + inclE c s hs (K' y))
    (hK : ContDiff ℝ 2 K) (hK' : ContDiff ℝ 2 K') :
    ∃ δK : (ℤ → ℂ) → ℝ,
      (∀ x₀ : FullWeightedHilbert c s, ∃ r > 0,
        ∃ (G : FullWeightedHilbert c s → ActualCM c) (η : (ℤ → ℂ) → ℝ),
          Set.EqOn G K (ball x₀ r) ∧
          IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η) ∧
      (∀ (x₀ : FullWeightedHilbert c s) (r : ℝ) (G : FullWeightedHilbert c s → ActualCM c)
          (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (ball x₀ r) →
          IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η →
          ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
            NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball x₀ r →
              δK z = η z) ∧
      let J : FullWeightedHilbert c s → ℝ := fun x =>
        |det2 (hsDerivH c s hs K x)| *
          Real.exp (-(δK (coordE c s x)) - ‖K x‖ ^ 2 / 2)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).map T.symm =
          (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
            (fun x => ENNReal.ofReal (J x)) ∧
      (∀ x, 0 < J x) ∧
      Integrable J (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
      ∫ x, J x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) = 1 ∧
      TendstoInMeasure (NlsGge.Measure.fullWeightSequenceGaussian c.val)
        (fun N z => finiteRamerDensity (fun v => v + truncField c s K N v) (headPt c N z))
        atTop (fun z => J (NlsGge.Measure.fullWeightedSequenceRealization c s z)) := by
  have hspec := Classical.choose_spec (divergence_identification c s hs K hK)
  have hdef : ramerDiv c s hs K = Classical.choose (divergence_identification c s hs K hK) := by
    unfold ramerDiv; rw [dif_pos hK]
  rw [← hdef] at hspec
  obtain ⟨hm, h2, h3, -, -⟩ := hspec
  refine ⟨ramerDiv c s hs K, h2, h3, ?_⟩
  intro J
  set γ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hγ
  have hJeq : J = ramerJE c s hs K (ramerDiv c s hs K) := by
    funext x; rw [ramerJE_eq]
  have hJeq' : J = ramerJac c s hs K := by
    funext x; rw [ramerJac_eq]
  have hpos : ∀ x, 0 < J x := by
    intro x
    rw [hJeq]
    exact ramerJE_pos c s hs T K K' hT hTs (hK.of_le (by norm_num)) (hK'.of_le (by norm_num))
      _ x
  obtain ⟨Jt, hJtm, hJae, hmap⟩ := ramer_step10_global c s hs T K K' hK hK' hT hTs
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
    exact aestronglyMeasurable_ramerJE c s hs K (hK.of_le (by norm_num)) _ hm
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
  · have hconv := tendstoInMeasure_cylindricalDensity c s hs K hK (ramerDiv c s hs K) h3
    refine TendstoInMeasure.congr (fun i => ae_eq_refl _) ?_ hconv
    filter_upwards [coordE_realization_ae c s hs] with z hz
    show ramerJ c s hs K (ramerDiv c s hs K) z = J (NlsGge.Measure.fullWeightedSequenceRealization c s z)
    simp only [J, ramerJ, hz]

/-- **Ramer's theorem, analytic form** (v2 `prop:gaussiancommon` hypotheses). -/
theorem ramer_eq_Ramercommon (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s)
    (T : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (K K' : FullWeightedHilbert c s → ActualCM c)
    (hT : ∀ x, T x = x + inclE c s hs (K x))
    (hTs : ∀ y, T.symm y = y + inclE c s hs (K' y))
    (hK : AnalyticOnNhd ℝ K Set.univ) (hK' : AnalyticOnNhd ℝ K' Set.univ) :
    ∃ δK : (ℤ → ℂ) → ℝ,
      (∀ x₀ : FullWeightedHilbert c s, ∃ r > 0,
        ∃ (G : FullWeightedHilbert c s → ActualCM c) (η : (ℤ → ℂ) → ℝ),
          Set.EqOn G K (ball x₀ r) ∧
          IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η) ∧
      (∀ (x₀ : FullWeightedHilbert c s) (r : ℝ) (G : FullWeightedHilbert c s → ActualCM c)
          (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (ball x₀ r) →
          IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η →
          ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
            NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball x₀ r →
              δK z = η z) ∧
      let J : FullWeightedHilbert c s → ℝ := fun x =>
        |det2 (hsDerivH c s hs K x)| *
          Real.exp (-(δK (coordE c s x)) - ‖K x‖ ^ 2 / 2)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).map T.symm =
          (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
            (fun x => ENNReal.ofReal (J x)) ∧
      (∀ x, 0 < J x) ∧
      Integrable J (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
      ∫ x, J x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) = 1 ∧
      TendstoInMeasure (NlsGge.Measure.fullWeightSequenceGaussian c.val)
        (fun N z => finiteRamerDensity (fun v => v + truncField c s K N v) (headPt c N z))
        atTop (fun z => J (NlsGge.Measure.fullWeightedSequenceRealization c s z)) :=
  ramer_eq_Ramercommon_C2 c s hs T K K' hT hTs hK.contDiff hK'.contDiff

#check @v2_divergence_unique
#check @ramer_eq_Ramercommon_C2
#check @ramer_eq_Ramercommon
#print axioms v2_divergence_unique
#print axioms ramer_eq_Ramercommon_C2
#print axioms ramer_eq_Ramercommon

end NlsGge.Ramer
