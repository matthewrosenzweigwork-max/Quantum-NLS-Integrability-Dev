import NlsGge.ThirdConsultation.AL.Basic
/- AL-115 production kit (proof development). Imports the landed AL Basic host for alTiltLimit38. -/
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

theorem al115 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ lower / 64) :
    let f : ℤ → ℝ := fun k => alTiltFactor38 c.val delta (2 * Real.pi * (k : ℝ)) 0
    Summable (fun k : ℤ => |Real.log (f k)|) ∧
    (∀ k : ℤ, 0 < f k) ∧
    HasSum (fun k : ℤ => Real.log (f k)) (Real.log (alTiltLimit38 c.val delta)) ∧
    0 < alTiltLimit38 c.val delta ∧
    HasProd f (alTiltLimit38 c.val delta) ∧
    Tendsto (fun N : ℕ => alTiltD38 c.val (alMeshStep38 N) delta N)
      atTop (𝓝 (alTiltLimit38 c.val delta)) := by
  intro f
  have hlo : 0 < lower := c.property.1
  have hc := c.property
  have hh0 : (0 : ℝ) ≤ lower / 2 := by linarith
  have hfpos : ∀ k : ℤ, 0 < f k := fun k => by
    have hb := alTiltFactor_bounds38 (c := c.val) hc hdelta0 hdelta hh0 (2 * Real.pi * (k : ℝ))
    exact lt_of_lt_of_le (by norm_num) hb.1
  have hdef : ∀ k : ℤ, |Real.log (f k)| ≤ 2 * alTiltMajorant38 lower delta k := by
    intro k
    have hω : 4 * |(k : ℝ)| ≤ |2 * Real.pi * (k : ℝ)| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
      have h3 : (4 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      have := mul_le_mul_of_nonneg_right h3 (abs_nonneg (k : ℝ))
      linarith
    have h1 := abs_log_factor_le38 (c := c.val) hc hdelta0 hdelta hh0 (2 * Real.pi * (k : ℝ))
    have h2 := deficit_le_majorant38 (c := c.val) hc hdelta0 hdelta hh0 (ν := k)
      (ω := 2 * Real.pi * (k : ℝ)) hω
    show |Real.log (alTiltFactor38 c.val delta (2 * Real.pi * (k : ℝ)) 0)| ≤ _
    linarith
  have hsumm : Summable (fun k : ℤ => |Real.log (f k)|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hdef
      ((summable_alTiltMajorant38 lower delta).mul_left 2)
  have hlogsum : Summable (fun k : ℤ => Real.log (f k)) := hsumm.of_abs
  have hHS : HasSum (fun k : ℤ => Real.log (f k)) (∑' k : ℤ, Real.log (f k)) :=
    hlogsum.hasSum
  have hP : HasProd f (Real.exp (∑' k : ℤ, Real.log (f k))) := by
    have h := hHS.rexp
    have e : (Real.exp ∘ fun k : ℤ => Real.log (f k)) = f :=
      funext fun k => Real.exp_log (hfpos k)
    rw [e] at h
    exact h
  have hlim : alTiltLimit38 c.val delta = Real.exp (∑' k : ℤ, Real.log (f k)) := rfl
  obtain ⟨Dδ, hDpos, hDP, hDT⟩ := alTiltD_tendsto38 (lo := lower) (up := upper) (c := c.val)
    hc hdelta0 hdelta
  have hDP' : HasProd f Dδ := by
    have e2 : (fun k : ℤ => 1 - delta * (1 + (2 * Real.pi * (k : ℝ)) ^ 4) /
        NlsGge.Weights.weight c.val (2 * Real.pi * (k : ℝ))) = f := by
      funext k
      show _ = alTiltFactor38 c.val delta (2 * Real.pi * (k : ℝ)) 0
      unfold alTiltFactor38
      rw [sub_zero]
    rw [e2] at hDP
    exact hDP
  have hDeq : Dδ = alTiltLimit38 c.val delta := by
    rw [hlim]
    exact hDP'.unique hP
  have hmesh : ∀ N : ℕ, alMeshStep38 N = alMesh38 N := fun N => by
    unfold alMeshStep38 alMesh38
    rw [one_div]
    push_cast
    ring_nf
  refine ⟨hsumm, hfpos, ?_, ?_, ?_, ?_⟩
  · rw [hlim, Real.log_exp]
    exact hHS
  · rw [hlim]
    exact Real.exp_pos _
  · rw [hlim]
    exact hP
  · rw [← hDeq]
    simp only [hmesh]
    exact hDT

end NlsGge.ThirdConsultation.AL
