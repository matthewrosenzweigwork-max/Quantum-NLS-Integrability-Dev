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

theorem al117 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ lower / 64)
    (N : ℕ) (hN : (3 * lower / 4)⁻¹ < ((2 * N + 1 : ℕ) : ℝ)) :
    let h : ℝ := alMeshStep38 N
    0 < alTiltD38 c.val h delta N ∧
    0 < alZ38 (L := 2 * N + 1) c.val h ∧
    0 < alZ38 (L := 2 * N + 1) (alTiltCoeff38 c.val delta) h ∧
    Integrable (fun alpha : ZMod (2 * N + 1) → ℂ =>
      Real.exp (delta * alTiltG38 h alpha)) (alEta38 (2 * N + 1) c.val h) ∧
    (∫ alpha, Real.exp (delta * alTiltG38 h alpha) ∂alEta38 (2 * N + 1) c.val h) =
      (alTiltD38 c.val h delta N)⁻¹ *
        (alZ38 (L := 2 * N + 1) (alTiltCoeff38 c.val delta) h /
          alZ38 (L := 2 * N + 1) c.val h) := by
  intro h
  have hh : h = ((2 * N + 1 : ℕ) : ℝ)⁻¹ := by
    show alMeshStep38 N = _
    unfold alMeshStep38
    rw [one_div]
    push_cast
    ring_nf
  obtain ⟨hint, ⟨hZ, -⟩, ⟨hZt, -⟩, hD, hI⟩ :=
    alTilt_identity_bundled38 (lo := lower) (up := upper) (c := c.val) c.property N hdelta0 hdelta hh hN
  exact ⟨hD, hZ, hZt, hint, hI⟩

end NlsGge.ThirdConsultation.AL
