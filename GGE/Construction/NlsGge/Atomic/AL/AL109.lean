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

theorem al109 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (N : ℕ) (k : ℤ) (hk : |k| ≤ (N : ℤ)) :
    let h : ℝ := alMeshStep38 N
    ∃ C delta : ℝ, 0 ≤ C ∧ 0 < delta ∧ h * delta ≤ 1 / 2 ∧
      ∀ t : ℝ, 0 < t → t ≤ delta →
      |alMass38 (2 * N + 1) (alPlaneWave38 (2 * N + 1) k t) -
        (h * t ^ 2 + h ^ 3 * t ^ 4 / 2)| ≤ C * t ^ 6 ∧
      alPlaneR38 c.val N k h t =
        alRemainder38 c.val h (ZMod.dft (alPlaneWave38 (2 * N + 1) k t)) ∧
      |alRemainder38 c.val h (ZMod.dft (alPlaneWave38 (2 * N + 1) k t)) -
        (alBQuartic38 (weight c.val) h k - h ^ 3 / 2) * t ^ 4| ≤ C * t ^ 6 := by
  intro h
  have hh : h = 1 / ((2 * N + 1 : ℕ) : ℝ) := by
    show alMeshStep38 N = _
    unfold alMeshStep38
    push_cast
    ring_nf
  have hpos : 0 < h := by rw [hh]; positivity
  have hdpos : 0 < 1 / (2 * h) := by positivity
  obtain ⟨C₁, δ₁, hδ₁, hM⟩ := alPlane_mass_expansion38 N k hh
  obtain ⟨C₂, δ₂, hδ₂, hR⟩ := alPlane_R_expansion38 (c := c.val) c.property N k hk hh
  refine ⟨|C₁| + |C₂|, min (min δ₁ δ₂) (1 / (2 * h)),
    by positivity, lt_min (lt_min hδ₁ hδ₂) hdpos, ?_, fun t ht0 ht => ?_⟩
  · calc h * min (min δ₁ δ₂) (1 / (2 * h)) ≤ h * (1 / (2 * h)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hpos.le
      _ = 1 / 2 := by field_simp
  have ht6 : (0 : ℝ) ≤ t ^ 6 := by positivity
  have hd1 : t ≤ δ₁ := ht.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hd2 : t ≤ δ₂ := ht.trans ((min_le_left _ _).trans (min_le_right _ _))
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (hM t ht0 hd1) (mul_le_mul_of_nonneg_right
      (by linarith [le_abs_self C₁, abs_nonneg C₂]) ht6)
  · exact (alRemainder_plane38 c.val N k hk h t).symm
  · rw [alRemainder_plane38 c.val N k hk h t]
    exact le_trans (hR t ht0 hd2) (mul_le_mul_of_nonneg_right
      (by linarith [le_abs_self C₂, abs_nonneg C₁]) ht6)

end NlsGge.ThirdConsultation.AL
