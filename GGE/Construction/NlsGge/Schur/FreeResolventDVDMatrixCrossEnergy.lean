import NlsGge.Schur.FreeResolventPotentialMatrixEntryBoundsAllIndices
import NlsGge.Analysis.PhysicalNonresonantSeries

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

private def sectorIndexEquiv (n : ℤ) : ℤ ≃ Sector n :=
  Equiv.ofBijective (sectorIndex n)
    ⟨sectorIndex_injective n, sectorIndex_covers n⟩

/-- The actual upper DVD cross-parity matrix energy is bounded by the source
double Fourier sum, with every signed output and input mode included. -/
theorem freeResolventDVD_upper_matrix_energy_bound
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    (∑' ml : Sector n × Sector n,
      ENNReal.ofReal
        (‖inner ℂ (parityPairVector n (true, ml.1))
          (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
            (parityPairVector n (false, ml.2)))‖ ^ 2)) ≤
      ENNReal.ofReal
        ((2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
          ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2) := by
  let e : ℤ × ℤ ≃ Sector n × Sector n :=
    (sectorIndexEquiv n).prodCongr (sectorIndexEquiv n)
  have hsource : Summable (fun rs : ℤ × ℤ =>
      ‖physicalFourier u₁ (n + rs.1 + rs.2)‖ ^ 2 *
        inverseSquare rs.1 * inverseSquare rs.2) :=
    physicalH1_source_double_summable u₁ hu₁ n
  calc
    (∑' ml : Sector n × Sector n,
      ENNReal.ofReal
        (‖inner ℂ (parityPairVector n (true, ml.1))
          (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
            (parityPairVector n (false, ml.2)))‖ ^ 2)) =
      ∑' rs : ℤ × ℤ,
        ENNReal.ofReal
          (‖inner ℂ (parityPairVector n (true, sectorIndex n rs.1))
            (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
              (parityPairVector n (false, sectorIndex n rs.2)))‖ ^ 2) := by
        symm
        exact e.tsum_eq (fun ml : Sector n × Sector n =>
          ENNReal.ofReal
            (‖inner ℂ (parityPairVector n (true, ml.1))
              (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
                (parityPairVector n (false, ml.2)))‖ ^ 2))
    _ ≤ ∑' rs : ℤ × ℤ,
        ENNReal.ofReal
          (‖physicalFourier u₁ (n + rs.1 + rs.2)‖ ^ 2 *
            inverseSquare rs.1 * inverseSquare rs.2) :=
      ENNReal.tsum_le_tsum (fun rs => ENNReal.ofReal_le_ofReal
        (freeResolventPotentialFreeResolvent_upper_entry_sq_bound_all
          u₁ u₂ hu₁ hu₂ n z hz rs.1 rs.2))
    _ = ENNReal.ofReal
        (∑' rs : ℤ × ℤ,
          ‖physicalFourier u₁ (n + rs.1 + rs.2)‖ ^ 2 *
            inverseSquare rs.1 * inverseSquare rs.2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun rs => mul_nonneg (mul_nonneg (sq_nonneg _) (inverseSquare_nonneg _))
          (inverseSquare_nonneg _)) hsource]
    _ ≤ ENNReal.ofReal
        ((2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
          ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal (physicalH1_source_double_tsum_bound u₁ hu₁ n)

/-- The independent reflected lower DVD cross-parity matrix energy is bounded
by the reflected physical H¹ double sum. -/
theorem freeResolventDVD_lower_matrix_energy_bound
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    (∑' ml : Sector n × Sector n,
      ENNReal.ofReal
        (‖inner ℂ (parityPairVector n (false, ml.1))
          (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
            (parityPairVector n (true, ml.2)))‖ ^ 2)) ≤
      ENNReal.ofReal
        ((2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
          ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2) := by
  let e : ℤ × ℤ ≃ Sector n × Sector n :=
    (sectorIndexEquiv n).prodCongr (sectorIndexEquiv n)
  have hsource : Summable (fun rs : ℤ × ℤ =>
      ‖physicalFourier u₂ (-(n + rs.1 + rs.2))‖ ^ 2 *
        inverseSquare rs.1 * inverseSquare rs.2) :=
    physicalH1_reflected_double_summable u₂ hu₂ n
  calc
    (∑' ml : Sector n × Sector n,
      ENNReal.ofReal
        (‖inner ℂ (parityPairVector n (false, ml.1))
          (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
            (parityPairVector n (true, ml.2)))‖ ^ 2)) =
      ∑' rs : ℤ × ℤ,
        ENNReal.ofReal
          (‖inner ℂ (parityPairVector n (false, sectorIndex n rs.1))
            (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
              (parityPairVector n (true, sectorIndex n rs.2)))‖ ^ 2) := by
        symm
        exact e.tsum_eq (fun ml : Sector n × Sector n =>
          ENNReal.ofReal
            (‖inner ℂ (parityPairVector n (false, ml.1))
              (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
                (parityPairVector n (true, ml.2)))‖ ^ 2))
    _ ≤ ∑' rs : ℤ × ℤ,
        ENNReal.ofReal
          (‖physicalFourier u₂ (-(n + rs.1 + rs.2))‖ ^ 2 *
            inverseSquare rs.1 * inverseSquare rs.2) :=
      ENNReal.tsum_le_tsum (fun rs => ENNReal.ofReal_le_ofReal
        (freeResolventPotentialFreeResolvent_lower_entry_sq_bound_all
          u₁ u₂ hu₁ hu₂ n z hz rs.1 rs.2))
    _ = ENNReal.ofReal
        (∑' rs : ℤ × ℤ,
          ‖physicalFourier u₂ (-(n + rs.1 + rs.2))‖ ^ 2 *
            inverseSquare rs.1 * inverseSquare rs.2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun rs => mul_nonneg (mul_nonneg (sq_nonneg _) (inverseSquare_nonneg _))
          (inverseSquare_nonneg _)) hsource]
    _ ≤ ENNReal.ofReal
        ((2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
          ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal (physicalH1_reflected_double_tsum_bound u₂ hu₂ n)

end NlsGge.Schur
