import NlsGge.Hierarchy.ALQ4Limit38
import NlsGge.Hierarchy.ALFreeFields38
import NlsGge.Hierarchy.ALCorrector38
import NlsGge.Hierarchy.ALFreeDeterminant38
import NlsGge.Hierarchy.ALRatesBridge38
import NlsGge.Hierarchy.ALCompactConsistency38
import NlsGge.Hierarchy.ALPlaneConsistency38
import NlsGge.Hierarchy.ALNegativeQuartic38
import NlsGge.Hierarchy.ALTiltMeasure38
import NlsGge.Birkhoff.W04WeightedSmoothing38
import NlsGge.Birkhoff.S05FreeEnergy38b
import NlsGge.Hierarchy.ALEnergyAnalytic38
import NlsGge.Hierarchy.ALPositiveDecompositions38
import NlsGge.Hierarchy.ALFiniteMeasure38
import NlsGge.Hierarchy.ALMoments38
import NlsGge.Hierarchy.ALFullEnergy38
import NlsGge.Hierarchy.ALTransferDefs38
import NlsGge.Hierarchy.ALSampling38
import NlsGge.Hierarchy.ALSamplingV2Formula38
import NlsGge.Hierarchy.ALQ4Ensemble38
import NlsGge.Hierarchy.ALQ4Gaussian38
import NlsGge.Hierarchy.ALGaussianNormalizer38
import NlsGge.Hierarchy.ALTilt38
import NlsGge.Hierarchy.ALLaurent38
import NlsGge.Hierarchy.ALExteriorBranch38
import NlsGge.Hierarchy.ALQuadraticPart38
import NlsGge.Hierarchy.ALIsospectral38
import NlsGge.Hierarchy.ALGlobalFlow38
import NlsGge.Hierarchy.ALLiouvilleInvariance38
import NlsGge.Hierarchy.ALBoundaryKappa38
import NlsGge.Hierarchy.ALPoissonLiouville38
import NlsGge.Hierarchy.ALComplexMonodromy38
import NlsGge.Hierarchy.ALComplexExteriorLog38
import NlsGge.Hierarchy.ALPlaneWaveGap38
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38
import NlsGge.Spectral.ActualComplexZsDysonProductHasSumV2
import NlsGge.Analysis.NaturalCover
import NlsGge.Definitions.PilotInterfaces
import NlsGge.Schur.FourierMultiplier
import NlsGge.Sobolev.SourceWeighted
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Sobolev.FiniteFourier
import NlsGge.Birkhoff.F08Bare38g
import NlsGge.Birkhoff.F08Bare38d
import NlsGge.Birkhoff.F05Identity38
import NlsGge.Bootstrap

open scoped Nat
open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core
open Set Filter Topology

namespace NlsGge.ThirdConsultation.AL

theorem al011 {L : ℕ} [NeZero L] (α : ZMod L → ℂ)
    (hα : IsALField38 α) :
  AnalyticOnNhd ℂ (alLog38 α) (Metric.ball (0 : ℂ) 1) ∧
  alLog38 α 0 = ((alMass38 L α / 2 : ℝ) : ℂ) ∧
  (∀ ζ ∈ Metric.ball (0 : ℂ) 1,
    Complex.exp (alLog38 α ζ) = alExteriorG38 α ζ ∧
    alLog38 α (-ζ) = alLog38 α ζ) ∧
  (∀ ℓ : ℂ → ℂ,
    AnalyticOnNhd ℂ ℓ (Metric.ball (0 : ℂ) 1) →
    (∀ ζ ∈ Metric.ball (0 : ℂ) 1, Complex.exp (ℓ ζ) = alExteriorG38 α ζ) →
    ℓ 0 = ((alMass38 L α / 2 : ℝ) : ℂ) →
      Set.EqOn ℓ (alLog38 α) (Metric.ball (0 : ℂ) 1)) ∧
  (∀ k : ℕ, alC38 α k =
    iteratedDeriv (2*k) (alLog38 α) 0 / ((2*k)! : ℂ)) ∧
  ∀ z : ℂ, 1 < ‖z‖ →
    Complex.exp ((L : ℂ)*alPMinusLog38 α z) = alExtW38 α z⁻¹/z^L ∧
    HasSum (fun k : ℕ => alC38 α (k+1) * z⁻¹^(2*(k+1)))
      ((L : ℂ)*alPMinusLog38 α z - ((alMass38 L α / 2 : ℝ) : ℂ)) := by
  have hs := alLog38_spec hα
  -- identity-theorem uniqueness of analytic logarithms on the unit ball
  have hU : ∀ ℓ1 ℓ2 : ℂ → ℂ, AnalyticOnNhd ℂ ℓ1 (Metric.ball (0 : ℂ) 1) →
      AnalyticOnNhd ℂ ℓ2 (Metric.ball (0 : ℂ) 1) →
      (∀ ζ ∈ Metric.ball (0 : ℂ) 1, Complex.exp (ℓ1 ζ) = Complex.exp (ℓ2 ζ)) →
      ℓ1 0 = ℓ2 0 → ∀ ζ ∈ Metric.ball (0 : ℂ) 1, ℓ1 ζ = ℓ2 ζ := by
    intro ℓ1 ℓ2 h1 h2 hexp h0
    have hcont : ∀ ζ ∈ Metric.ball (0 : ℂ) 1,
        ContinuousAt (fun ζ => ℓ1 ζ - ℓ2 ζ) ζ := fun ζ hζ =>
      ((h1 ζ hζ).continuousAt.sub (h2 ζ hζ).continuousAt)
    have hlocal : ∀ ζ0 ∈ Metric.ball (0 : ℂ) 1, ℓ1 ζ0 - ℓ2 ζ0 = 0 →
        ∀ᶠ ζ in nhds ζ0, ℓ1 ζ - ℓ2 ζ = 0 := by
      intro ζ0 hζ0 hd0
      have hball : Metric.ball (ℓ1 ζ0 - ℓ2 ζ0) (2 * Real.pi) ∈ nhds (ℓ1 ζ0 - ℓ2 ζ0) :=
        Metric.ball_mem_nhds _ (by positivity)
      have hpre := (hcont ζ0 hζ0).preimage_mem_nhds hball
      filter_upwards [Metric.isOpen_ball.mem_nhds hζ0, hpre] with ζ hζb hζn
      have hn : ‖ℓ1 ζ - ℓ2 ζ‖ < 2 * Real.pi := by
        have h' := hζn
        rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, hd0, sub_zero] at h'
        exact h'
      have he : Complex.exp (ℓ1 ζ - ℓ2 ζ) = 1 := by
        rw [Complex.exp_sub, hexp ζ hζb, div_self (Complex.exp_ne_zero _)]
      obtain ⟨n, hn'⟩ := Complex.exp_eq_one_iff.1 he
      have hnorm : ‖ℓ1 ζ - ℓ2 ζ‖ = |(n : ℝ)| * (2 * Real.pi) := by
        rw [hn']
        simp [norm_mul, abs_of_pos Real.pi_pos]
      have habs : |(n : ℝ)| < 1 := by
        rw [hnorm] at hn
        nlinarith [Real.pi_pos]
      have hn0 : n = 0 := by
        have : |n| < 1 := by exact_mod_cast habs
        exact Int.abs_lt_one_iff.mp this
      rw [hn', hn0]
      simp
    have hAopen : IsOpen {ζ : ℂ | ζ ∈ Metric.ball (0 : ℂ) 1 ∧ ℓ1 ζ - ℓ2 ζ = 0} := by
      rw [isOpen_iff_mem_nhds]
      rintro ζ0 ⟨hb, hd0⟩
      filter_upwards [hlocal ζ0 hb hd0, Metric.isOpen_ball.mem_nhds hb] with ζ h1' h2'
      exact ⟨h2', h1'⟩
    have hclos : closure {ζ : ℂ | ζ ∈ Metric.ball (0 : ℂ) 1 ∧ ℓ1 ζ - ℓ2 ζ = 0} ∩
        Metric.ball (0 : ℂ) 1 ⊆ {ζ : ℂ | ζ ∈ Metric.ball (0 : ℂ) 1 ∧ ℓ1 ζ - ℓ2 ζ = 0} := by
      rintro ζ1 ⟨hcl, hb1⟩
      refine ⟨hb1, ?_⟩
      by_contra hne
      have hpos : 0 < ‖ℓ1 ζ1 - ℓ2 ζ1‖ := norm_pos_iff.2 hne
      have hpre := (hcont ζ1 hb1).preimage_mem_nhds
        (Metric.ball_mem_nhds (ℓ1 ζ1 - ℓ2 ζ1) hpos)
      obtain ⟨ζ, hζpre, hζA⟩ := mem_closure_iff_nhds.1 hcl _ hpre
      have hz0 : ℓ1 ζ - ℓ2 ζ = 0 := hζA.2
      rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, hz0, zero_sub, norm_neg] at hζpre
      exact lt_irrefl _ hζpre
    have hsub := (convex_ball (0 : ℂ) 1).isPreconnected.subset_of_closure_inter_subset hAopen
      ⟨0, Metric.mem_ball_self one_pos, Set.mem_setOf_eq ▸ ⟨Metric.mem_ball_self one_pos,
        sub_eq_zero.2 h0⟩⟩ hclos
    exact fun ζ hζ => sub_eq_zero.1 (hsub hζ).2
  refine ⟨hs.1, hs.2.2.1, fun ζ hζ => ⟨hs.2.1 ζ hζ, hs.2.2.2 ζ hζ⟩, ?_, fun k => rfl,
    fun z hz => ⟨alPMinusLog38_exp hα hz, ?_⟩⟩
  · intro ℓ hℓ hexp h0
    exact hU ℓ (alLog38 α) hℓ hs.1 (fun ζ hζ => by rw [hexp ζ hζ, hs.2.1 ζ hζ])
      (by rw [h0, hs.2.2.1]) 
  · obtain ⟨hsum, heq⟩ := alPMinusLog38_laurent hα hz
    have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
    have key : (L : ℂ) * alPMinusLog38 α z - ((alMass38 L α / 2 : ℝ) : ℂ) =
        ∑' k : ℕ, alC38 α (k + 1) * z⁻¹ ^ (2 * (k + 1)) := by
      rw [heq]
      push_cast
      field_simp
      ring
    rw [key]
    exact hsum.hasSum

end NlsGge.ThirdConsultation.AL
