import NlsGge.Hierarchy.ALQ4Ensemble38
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

theorem al055 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁)
    (h2 : 0 < β₂) (N : ℕ) (hh : alh38 N < β₀) :
    (∀ v : ZMod (2 * N + 1) → ℂ,
      (∀ j, alh38 N * ‖v j‖ < 1) → 0 ≤ alRh38 β₀ β₁ β₂ N v) ∧
    (∀ v : ZMod (2 * N + 1) → ℂ,
      0 ≤ alQ4F38 β₀ β₁ β₂ N v ∧ alQ4F38 β₀ β₁ β₂ N v ≤ 1) := by
  by_cases hN : 1 ≤ N
  · exact ⟨fun v hv => alRh38_nonneg h1.le h2.le hN hh v hv, fun v => ⟨alQ4F_nonneg38 _ _ _ _ v,
      alQ4F_le_one38 h1.le h2.le hN hh v⟩⟩
  · obtain rfl : N = 0 := by omega
    have hsub : ∀ j : ZMod (2 * 0 + 1), j = 0 := by decide
    have hS : ∀ {M : Type} [AddCommMonoid M] (f : ZMod (2 * 0 + 1) → M), ∑ j, f j = f 0 :=
      fun f => Finset.sum_eq_single 0 (fun j _ hj => absurd (hsub j) hj)
        (fun h => absurd (Finset.mem_univ _) h)
    have hz1 : ∀ j : ZMod (2 * 0 + 1), j - 1 = 0 := fun j => by rw [hsub j]; rfl
    have hz2 : ∀ j : ZMod (2 * 0 + 1), j - 2 = 0 := fun j => by rw [hsub j]; rfl
    have hneg : (-1 : ZMod (2 * 0 + 1)) = 0 := hsub _
    have halh : alh38 0 = 1 := by simp [alh38]
    have key : ∀ v : ZMod (2 * 0 + 1) → ℂ, (∀ j, alh38 0 * ‖v j‖ < 1) →
        0 ≤ alRh38 β₀ β₁ β₂ 0 v ∧ alRh38 β₀ β₁ β₂ 0 v = (β₀ - 1) * alEll (‖v 0‖ ^ 2) +
          2 * β₁ * alEll (‖v 0‖ ^ 2) + 6 * β₂ * (alEll (‖v 0‖ ^ 2) - (‖v 0‖ ^ 2) ^ 2 / 2) := by
      intro v hv
      have hv0 : ‖v 0‖ < 1 := by have := hv 0; rwa [halh, one_mul] at this
      have hr0 : 0 ≤ ‖v 0‖ ^ 2 := by positivity
      have hr1 : ‖v 0‖ ^ 2 < 1 := by nlinarith [norm_nonneg (v 0)]
      have hC1 : (v 0 * (starRingEnd ℂ) (v 0)).re = ‖v 0‖ ^ 2 := by
        rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      have hC1c : v 0 * (starRingEnd ℂ) (v 0) = ((‖v 0‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hM : alMd (fun j => ((alh38 0 : ℝ) : ℂ) * v j) = -Real.log (1 - ‖v 0‖ ^ 2) := by
        unfold alMd
        rw [hS]
        simp [alR, halh, hneg]
      have hHd : alHd (fun j => ((alh38 0 : ℝ) : ℂ) * v j) = 2 * alMd (fun j => ((alh38 0 : ℝ) : ℂ) * v j) - 2 * ‖v 0‖ ^ 2 := by
        unfold alHd alC1
        rw [hS]
        simp [halh, hC1, hneg]
      have hC2 : (alC2 (fun j => ((alh38 0 : ℝ) : ℂ) * v j)).re = ‖v 0‖ ^ 2 - 3 / 2 * ‖v 0‖ ^ 4 := by
        unfold alC2
        rw [hS, hS]
        simp only [halh, Complex.ofReal_one, one_mul, hz1, hz2, alR, hC1c]
        simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two, mul_comm]
        ring
      have hKd : alKd (fun j => ((alh38 0 : ℝ) : ℂ) * v j) = 6 * alMd (fun j => ((alh38 0 : ℝ) : ℂ) * v j) - 8 * (alC1 (fun j => ((alh38 0 : ℝ) : ℂ) * v j)).re + 2 * (alC2 (fun j => ((alh38 0 : ℝ) : ℂ) * v j)).re := rfl
      have hC1r : (alC1 (fun j => ((alh38 0 : ℝ) : ℂ) * v j)).re = ‖v 0‖ ^ 2 := by
        unfold alC1
        rw [hS]
        simp [halh, hneg, hC1]
      have hsumT : ∑ k ∈ Finset.Icc (0 : ℤ) 0, alSymbol38 β₀ β₁ β₂ 0 k * ‖alDFT38 0 v k‖ ^ 2 =
          (β₀ - 1) * ‖v 0‖ ^ 2 := by
        have hI : Finset.Icc (0 : ℤ) 0 = {0} := by simp
        rw [hI, Finset.sum_singleton]
        have hdef : ∀ x : ZMod (2 * 0 + 1), ‖v x‖ = ‖v 0‖ := fun x => by rw [hsub x]
        simp [alDFT38, alSymbol38, alomega38, halh, hS, hdef]
      have hfin : alRh38 β₀ β₁ β₂ 0 v = (β₀ - 1) * alMd (fun j => ((alh38 0 : ℝ) : ℂ) * v j) + β₁ * alHd (fun j => ((alh38 0 : ℝ) : ℂ) * v j) + β₂ * alKd (fun j => ((alh38 0 : ℝ) : ℂ) * v j) - (β₀ - 1) * ‖v 0‖ ^ 2 := by
        unfold alRh38
        simp only [Nat.cast_zero, neg_zero]
        rw [hsumT, halh]
        simp
      have hr0' : 0 ≤ ‖v 0‖ ^ 2 := by positivity
      have hr1' : ‖v 0‖ ^ 2 < 1 := by nlinarith [norm_nonneg (v 0)]
      have heq : alRh38 β₀ β₁ β₂ 0 v = (β₀ - 1) * alEll (‖v 0‖ ^ 2) +
          2 * β₁ * alEll (‖v 0‖ ^ 2) + 6 * β₂ * (alEll (‖v 0‖ ^ 2) - (‖v 0‖ ^ 2) ^ 2 / 2) := by
        rw [hfin, hHd, hKd, hC2, hC1r, hM]
        unfold alEll
        ring
      have hb0 : 0 ≤ β₀ - 1 := by
        have : alh38 0 < β₀ := hh
        rw [halh] at this
        linarith
      have hE0 : 0 ≤ alEll (‖v 0‖ ^ 2) := alEll_nonneg hr0' hr1'
      have hE2 : 0 ≤ alEll (‖v 0‖ ^ 2) - (‖v 0‖ ^ 2) ^ 2 / 2 := by
        have := alEll_sq_nonneg hr0' hr1'
        unfold alEll
        linarith
      refine ⟨?_, heq⟩
      rw [heq]
      have t1 := mul_nonneg hb0 hE0
      have t2 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h1.le) hE0
      have t3 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) h2.le) hE2
      linarith
    refine ⟨fun v hv => (key v hv).1, fun v => ⟨alQ4F_nonneg38 _ _ _ _ v, ?_⟩⟩
    unfold alQ4F38
    split_ifs with hv
    · rw [Real.exp_le_one_iff]
      have := (key v hv).1
      linarith
    · norm_num

end NlsGge.ThirdConsultation.AL
