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

theorem al025 {L : ℕ} [NeZero L]
    (α : ZMod L → ℂ) (hα : IsALField38 α) (j : ℕ) :
  alK38 α j =
    (Nat.choose (2*j) j : ℝ)*alMass38 L α +
      2*∑ k ∈ Finset.Icc 1 j,
        (-1 : ℝ)^k*(Nat.choose (2*j) (j-k) : ℝ)*(alC38 α k).re ∧
  alMomentK38 α j = alK38 α j ∧
  IntervalIntegrable
    (fun θ : ℝ => (2-2*Real.cos (2*θ))^j*alKappa38 α θ) volume 0 (2*Real.pi) ∧
  alK38 α j = (L/Real.pi) *
    ∫ θ in (0 : ℝ)..2*Real.pi, (2-2*Real.cos (2*θ))^j*alKappa38 α θ := by
  refine ⟨rfl, alMomentK38_eq_alK38 α j, ?_, alK38_spectral hα j⟩
  have hc : Continuous fun θ : ℝ => (2 - 2 * Real.cos (2 * θ)) ^ j * alKappa38 α θ :=
    (by fun_prop : Continuous fun θ : ℝ => (2 - 2 * Real.cos (2 * θ)) ^ j).mul
      (continuous_alKappa38 hα)
  exact hc.intervalIntegrable _ _

end NlsGge.ThirdConsultation.AL
