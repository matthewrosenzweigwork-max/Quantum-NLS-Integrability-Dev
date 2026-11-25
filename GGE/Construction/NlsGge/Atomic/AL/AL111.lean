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
open NlsGge.Pilot NlsGge.Weights
open Set Filter Topology MeasureTheory

namespace NlsGge.ThirdConsultation.AL

theorem al111 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    ∀ᶠ N : ℕ in atTop, ∃ delta : ℝ, 0 < delta ∧
      ∀ t : ℝ, 0 < t → t < delta →
      IsALField38 (alPlaneWave38 (2 * N + 1) (N : ℤ) t) ∧
      alRemainder38 c.val (alMeshStep38 N)
        (ZMod.dft (alPlaneWave38 (2 * N + 1) (N : ℤ) t)) < 0 ∧
      1 < alReweight38 c.val (alMeshStep38 N)
        (ZMod.dft (alPlaneWave38 (2 * N + 1) (N : ℤ) t)) := by
  obtain ⟨h₀, hh₀, hanch⟩ := alPlane_negative_remainder38 (c := c.val) c.property
  have hT : Tendsto (fun N : ℕ => alMeshStep38 N) atTop (𝓝 0) := by
    have hg : Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
    exact (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hg
  have hev : ∀ᶠ N : ℕ in atTop, alMeshStep38 N < h₀ := (tendsto_order.1 hT).2 h₀ hh₀
  filter_upwards [hev] with N hN
  have hh : alMeshStep38 N = 1 / ((2 * N + 1 : ℕ) : ℝ) := by
    unfold alMeshStep38
    push_cast
    ring_nf
  obtain ⟨t₀, ht₀, hbound⟩ := (hanch N (alMeshStep38 N) hh hN.le).2
  exact ⟨t₀ / 2, by positivity, fun t ht0 ht => hbound t ht0 (by linarith)⟩

end NlsGge.ThirdConsultation.AL
