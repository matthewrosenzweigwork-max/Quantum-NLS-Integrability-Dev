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

theorem al021 {L : ℕ} [NeZero L]
    (α : ZMod L → ℂ) (hα : IsALField38 α) (t : ℝ) :
  alMass38 L (alFlow38 alHd t α) = alMass38 L α ∧
  (∀ z : ℂ, 1 < ‖z‖ →
    alExtW38 (alFlow38 alHd t α) z⁻¹ = alExtW38 α z⁻¹) ∧
  Set.EqOn (alLog38 (alFlow38 alHd t α)) (alLog38 α) (Metric.ball (0 : ℂ) 1) ∧
  (∀ z : ℂ, 1 < ‖z‖ →
    alPMinusLog38 (alFlow38 alHd t α) z = alPMinusLog38 α z) ∧
  ∀ k : ℕ, alC38 (alFlow38 alHd t α) k = alC38 α k
 := by
  have hH : ContDiffOn ℝ 2 alHd (alDisk38 L) := alHd_contDiffOn38 (L := L)
  have hcons := alBracket_mass_alHd38 (L := L)
  have hfl := alFlow_spec38 hH hcons hα
  have hγ : ∀ τ ∈ (Set.univ : Set ℝ), IsALField38 (alFlow38 alHd τ α) ∧
      HasDerivAt (fun τ => alFlow38 alHd τ α) (alX38 alHd (alFlow38 alHd τ α)) τ :=
    fun τ _ => hfl.2 τ
  have hstart : alFlow38 alHd 0 α = α := hfl.1
  have htr : ∀ τ z, z ≠ 0 →
      Matrix.trace (alMonodromy38 (alFlow38 alHd τ α) z) = Matrix.trace (alMonodromy38 α z) := by
    intro τ z hz
    have := trace_alMonodromy_const38 (U := Set.univ) isOpen_univ isPreconnected_univ hγ hz
      (Set.mem_univ τ) (Set.mem_univ 0)
    exact this.trans (congrArg (fun β => Matrix.trace (alMonodromy38 β z)) hstart)
  have hmass : ∀ τ, alMass38 L (alFlow38 alHd τ α) = alMass38 L α := by
    intro τ
    have := alMass_const38 (U := Set.univ) isOpen_univ isPreconnected_univ hγ
      (Set.mem_univ τ) (Set.mem_univ 0)
    exact this.trans (congrArg (alMass38 L) hstart)
  have hG : ∀ τ, ∀ ζ ∈ Metric.ball (0 : ℂ) 1,
      alExteriorG38 (alFlow38 alHd τ α) ζ = alExteriorG38 α ζ := fun τ ζ hζ =>
    alExteriorG38_eq_of_trace38 (hfl.2 τ).1 hα (fun z hz => htr τ z hz) ζ hζ
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
  have hLog : ∀ τ, Set.EqOn (alLog38 (alFlow38 alHd τ α)) (alLog38 α) (Metric.ball (0 : ℂ) 1) :=
    fun τ ζ hζ => hU _ _ (alLog38_spec (hfl.2 τ).1).1 (alLog38_spec hα).1
      (fun ζ' hζ' => by
        rw [(alLog38_spec (hfl.2 τ).1).2.1 ζ' hζ', (alLog38_spec hα).2.1 ζ' hζ', hG τ ζ' hζ'])
      (by rw [(alLog38_spec (hfl.2 τ).1).2.2.1, (alLog38_spec hα).2.2.1, hmass τ]) ζ hζ
  refine ⟨hmass t, fun z hz => ?_, fun ζ hζ => hLog t hζ, fun z hz => ?_, fun k => ?_⟩
  · unfold alExtW38
    rw [hG t z⁻¹ (inv_mem_ball38 hz)]
  · unfold alPMinusLog38
    rw [hLog t (inv_mem_ball38 hz)]
  · have := alC_const38 (U := Set.univ) isOpen_univ isPreconnected_univ hγ
      (Set.mem_univ t) (Set.mem_univ 0) k
    exact this.trans (congrArg (fun β => alC38 β k) hstart)

end NlsGge.ThirdConsultation.AL
