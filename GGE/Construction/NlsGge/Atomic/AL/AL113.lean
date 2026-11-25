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

theorem al113 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ lower / 64)
    (N : ℕ) (hN : alMeshStep38 N ≤ c.val 0 / 2) :
    ∀ k : ℤ, |k| ≤ (N : ℤ) →
      let h : ℝ := alMeshStep38 N
      let omega : ℝ := alOmegaFree38 N k
      let d : ℝ := delta * (1 + omega ^ 4) / alRateFree38 c.val N k
      0 < alRateFree38 c.val N k ∧ 0 ≤ d ∧ d ≤ 1 / 2 ∧
      0 < alTiltFactor38 c.val delta omega h ∧
      Real.exp (Real.log (alTiltFactor38 c.val delta omega h)) =
        alTiltFactor38 c.val delta omega h := by
  have hlo : 0 < lower := c.property.1
  have hc := c.property
  have hnn : ∀ (r : ℝ) (i : ℕ), 0 ≤ NlsGge.weightTerm c.val r i := fun r i => by
    unfold NlsGge.weightTerm NlsGge.coefficient
    have hci : 0 ≤ c.val i / (Nat.factorial i : ℝ) ^ 4 :=
      div_nonneg (by linarith [(c.property.2.2 i).1]) (by positivity)
    exact mul_nonneg hci (by rw [pow_mul]; positivity)
  have hc0 : ∀ r : ℝ, c.val 0 ≤ NlsGge.Weights.weight c.val r := fun r => by
    have hs := NlsGge.Weights.weightTerm_summable lower upper c.val hlo
      (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) r
    have h0 := hs.le_tsum 0 (fun i _ => hnn r i)
    have e : NlsGge.weightTerm c.val r 0 = c.val 0 := by
      unfold NlsGge.weightTerm NlsGge.coefficient
      simp
    have hw : NlsGge.Weights.weight c.val r = ∑' j, NlsGge.weightTerm c.val r j := rfl
    rw [hw]
    linarith
  intro k hk
  intro h omega d
  have hh : 0 < h := by
    show 0 < alMeshStep38 N
    unfold alMeshStep38
    positivity
  have hhle : h ≤ c.val 0 / 2 := hN
  have hW2 := weight_ge_two38 (lo := lower) (up := upper) (c := c.val) hc omega
  have hW0 := hc0 omega
  have hpos : 0 < NlsGge.Weights.weight c.val omega - h := by
    have : 0 < lower + lower / 16 * omega ^ 4 := by positivity
    linarith
  have hfac : alTiltFactor38 c.val delta omega h = 1 - d := by
    show 1 - delta * (1 + omega ^ 4) / (NlsGge.Weights.weight c.val omega - h) = 1 - d
    rfl
  have hdnn : 0 ≤ d := by
    show 0 ≤ delta * (1 + omega ^ 4) / alRateFree38 c.val N k
    exact div_nonneg (mul_nonneg hdelta0 (by positivity)) (by unfold alRateFree38; exact hpos.le)
  have hkey : delta * (1 + omega ^ 4) ≤ lower * (1 + omega ^ 4 / 16) / 4 := by
    have h1 : delta * (1 + omega ^ 4) ≤ lower / 64 * (1 + omega ^ 4) :=
      mul_le_mul_of_nonneg_right hdelta (by positivity)
    have h2 : lower / 64 * (1 + omega ^ 4) = lower * (1 + omega ^ 4 / 16) / 4 - lower * 15 / 64 := by
      ring
    linarith
  have hd_le : d ≤ 1 / 2 := by
    show delta * (1 + omega ^ 4) / alRateFree38 c.val N k ≤ 1 / 2
    unfold alRateFree38
    rw [div_le_iff₀ hpos]
    linarith
  have hfacpos : 0 < alTiltFactor38 c.val delta omega h := by
    rw [hfac]
    linarith
  refine ⟨?_, hdnn, hd_le, hfacpos, ?_⟩
  · unfold alRateFree38
    exact hpos
  · rw [Real.exp_log hfacpos]

end NlsGge.ThirdConsultation.AL
