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

theorem al116 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ lower / 64)
    (L : ℕ) [NeZero L] (h : ℝ) (hh : 0 < h) :
    (∀ alpha : ZMod L → ℂ, IsALField38 alpha →
      alEnergy38 c.val h alpha - delta * alTiltG38 h alpha =
        alEnergy38 (alTiltCoeff38 c.val delta) h alpha) ∧
    Integrable (alIntegrand38 (L := L) c.val h) ∧
    Integrable (alIntegrand38 (L := L) (alTiltCoeff38 c.val delta) h) ∧
    0 < alPartition38 L c.val h ∧
    0 < alPartition38 L (alTiltCoeff38 c.val delta) h ∧
    Integrable (fun alpha : ZMod L → ℂ => Real.exp (delta * alTiltG38 h alpha))
      (alEta38 L c.val h) ∧
    (∫ alpha, Real.exp (delta * alTiltG38 h alpha) ∂alEta38 L c.val h) =
      alPartition38 L (alTiltCoeff38 c.val delta) h / alPartition38 L c.val h := by
  have hc := c.property
  have hct := alTiltCoeff_admitted38 (lo := lower) (up := upper) (c := c.val) hc hdelta0 hdelta
  have hint := alTiltIntegral_eq_integral_eta38 (L := L) (lo := lower) (up := upper) (c := c.val)
    hc hdelta0 hdelta hh
  refine ⟨fun α hα => (alEnergy_tilt38 (L := L) (lo := lower) (up := upper) (c := c.val)
      hc hdelta0 hdelta hα hh).symm, (alPartition_bounds38 (L := L) hc hh).1,
    (alPartition_bounds38 (L := L) hct hh).1, (alPartition_bounds38 (L := L) hc hh).2.2.1,
    (alPartition_bounds38 (L := L) hct hh).2.2.1, hint.1, ?_⟩
  rw [hint.2.1, hint.2.2, inv_mul_eq_div]

end NlsGge.ThirdConsultation.AL
