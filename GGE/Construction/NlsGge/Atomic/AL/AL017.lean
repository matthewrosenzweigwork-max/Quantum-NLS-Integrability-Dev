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

theorem al017 {L : ℕ} [NeZero L] :
  (∀ (γ : ℝ → ZMod L → ℂ), IsAlGlobalCurve38 alHd γ →
    ∀ s t : ℝ, alMass38 L (γ t) = alMass38 L (γ s)) ∧
  (∀ R : ℝ, IsCompact (alMassSublevel38 L R) ∧
    alMassSublevel38 L R ⊆ alDisk38 L ∧
    ∀ α ∈ alMassSublevel38 L R, ∀ j : ZMod L,
      ‖α j‖^2 ≤ 1-Real.exp (-R))
 := by
  refine ⟨?_, ?_⟩
  · intro γ hγ s t
    exact alMass_const38 (U := Set.univ) isOpen_univ isPreconnected_univ
      (fun τ _ => hγ τ) (Set.mem_univ s) (Set.mem_univ t)
  · intro R
    have hexp : 0 < Real.exp (-R) := Real.exp_pos _
    have hmax : max (1 - Real.exp (-R)) 0 < 1 := max_lt (by linarith) one_pos
    have hr0lt : Real.sqrt (max (1 - Real.exp (-R)) 0) < 1 := by
      rw [Real.sqrt_lt' one_pos, one_pow]; exact hmax
    have hr0nn : 0 ≤ Real.sqrt (max (1 - Real.exp (-R)) 0) := Real.sqrt_nonneg _
    have hKdisk : Metric.closedBall (0 : ZMod L → ℂ)
        (Real.sqrt (max (1 - Real.exp (-R)) 0)) ⊆ alDisk38 L := by
      intro α hα
      rw [mem_closedBall_zero_iff] at hα
      show IsALField38 α
      intro j
      exact lt_of_le_of_lt (le_trans (norm_le_pi_norm α j) hα) hr0lt
    have hsub : alMassSublevel38 L R ⊆
        Metric.closedBall (0 : ZMod L → ℂ) (Real.sqrt (max (1 - Real.exp (-R)) 0)) := by
      intro α hα
      have hdisk : IsALField38 α := hα.1
      have hM : alMass38 L α ≤ R := hα.2
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg hr0nn).2 fun j => ?_
      have h1 := alNormSq_le_mass38 hdisk j
      have h2 : Real.exp (-R) ≤ Real.exp (-alMass38 L α) :=
        Real.exp_le_exp.2 (by linarith)
      have h3 : ‖α j‖ ^ 2 ≤ max (1 - Real.exp (-R)) 0 :=
        le_trans h1 (le_max_of_le_left (by linarith))
      calc ‖α j‖ = Real.sqrt (‖α j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (max (1 - Real.exp (-R)) 0) := Real.sqrt_le_sqrt h3
    have hcont : ContinuousOn (alMass38 L)
        (Metric.closedBall (0 : ZMod L → ℂ) (Real.sqrt (max (1 - Real.exp (-R)) 0))) :=
      fun α hα => (alMass_continuousAt38 (hKdisk hα)).continuousWithinAt
    have hset : alMassSublevel38 L R =
        Metric.closedBall (0 : ZMod L → ℂ) (Real.sqrt (max (1 - Real.exp (-R)) 0)) ∩
          alMass38 L ⁻¹' Set.Iic R := by
      ext α
      constructor
      · intro hα
        exact ⟨hsub hα, show alMass38 L α ≤ R from hα.2⟩
      · rintro ⟨hK', hM⟩
        exact ⟨hKdisk hK', show alMass38 L α ≤ R from hM⟩
    have hclosed : IsClosed (alMassSublevel38 L R) := by
      rw [hset]
      exact hcont.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Iic
    refine ⟨?_, ?_, ?_⟩
    · exact (isCompact_closedBall (0 : ZMod L → ℂ) _).of_isClosed_subset hclosed hsub
    · exact fun α hα => hKdisk (hsub hα)
    · intro α hα j
      have hdisk : IsALField38 α := hα.1
      have hM : alMass38 L α ≤ R := hα.2
      have h1 := alNormSq_le_mass38 hdisk j
      have h2 : Real.exp (-R) ≤ Real.exp (-alMass38 L α) :=
        Real.exp_le_exp.2 (by linarith)
      linarith

end NlsGge.ThirdConsultation.AL
