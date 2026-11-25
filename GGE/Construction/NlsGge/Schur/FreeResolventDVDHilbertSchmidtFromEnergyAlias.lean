import NlsGge.Schur.FreeResolventDVDMatrixEnergyReindex
import NlsGge.Schur.FreeResolventDVDMatrixEnergyToHS
import NlsGge.Schur.FreeResolventDVDMatrixCrossEnergy

set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- A named actual-operator alias keeps its concrete composition out of the
Hilbert--Schmidt theorem's type elaboration. It is definitionally the actual
`freeResolventPotentialFreeResolvent` continuous linear map. -/
def freeResolventPotentialFreeResolventOperator
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ParityPair n →L[ℂ] ParityPair n :=
  freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz

/-- The actual paired DVD operator is Hilbert--Schmidt, with the disk-uniform
source-H¹ bound. The public operator alias unfolds to the concrete composition. -/
theorem freeResolventPotentialFreeResolvent_isComplexHilbertSchmidt_from_matrix_energy
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    IsComplexHilbertSchmidt
        (freeResolventPotentialFreeResolventOperator u₁ u₂ hu₁ hu₂ n z hz) ∧
      complexHilbertSchmidtNorm
        (freeResolventPotentialFreeResolventOperator u₁ u₂ hu₁ hu₂ n z hz) ≤
        Real.sqrt
          ((2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2) *
            (‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 +
              ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2))) := by
  let T : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventPotentialFreeResolventOperator u₁ u₂ hu₁ hu₂ n z hz
  change IsComplexHilbertSchmidt T ∧ complexHilbertSchmidtNorm T ≤
    Real.sqrt
      ((2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2) *
        (‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 +
          ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2)))
  let B₁ := (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
    ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2
  let B₂ := (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
    ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2
  have hden : 0 ≤ 1 + (n : ℝ) ^ 2 := by positivity
  have hB₁ : 0 ≤ B₁ := by
    dsimp [B₁]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num) uniformConvolutionConstant_nonneg) hden)
      (sq_nonneg _)
  have hB₂ : 0 ≤ B₂ := by
    dsimp [B₂]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num) uniformConvolutionConstant_nonneg) hden)
      (sq_nonneg _)
  have hK : 0 ≤ B₁ + B₂ := add_nonneg hB₁ hB₂
  have henergy :
      (∑' input : Bool × Sector n, ∑' output : Bool × Sector n,
        ENNReal.ofReal
          (‖inner ℂ (parityPairVector n output)
            (T (parityPairVector n input))‖ ^ 2)) ≤ ENNReal.ofReal (B₁ + B₂) := by
    change (∑' input : Bool × Sector n, ∑' output : Bool × Sector n,
      ENNReal.ofReal
        (‖inner ℂ (parityPairVector n output)
          (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
            (parityPairVector n input))‖ ^ 2)) ≤ ENNReal.ofReal (B₁ + B₂)
    rw [freeResolventDVD_matrix_energy_eq_cross_from_reindex]
    calc
      _ ≤ ENNReal.ofReal B₁ + ENNReal.ofReal B₂ :=
        add_le_add
          (freeResolventDVD_upper_matrix_energy_bound u₁ u₂ hu₁ hu₂ n z hz)
          (freeResolventDVD_lower_matrix_energy_bound u₁ u₂ hu₁ hu₂ n z hz)
      _ = ENNReal.ofReal (B₁ + B₂) := by
        rw [← ENNReal.ofReal_add hB₁ hB₂]
  have henergy' :
      (∑' input : Bool × Sector n, ∑' output : Bool × Sector n,
        ENNReal.ofReal
          (‖inner ℂ (parityPairVector n output)
            (T (parityPairVector n input))‖ ^ 2)) ≤
        ENNReal.ofReal ((Real.sqrt (B₁ + B₂)) ^ 2) := by
    simpa only [Real.sq_sqrt hK] using henergy
  have hhs := freeResolventDVD_isComplexHilbertSchmidt_of_matrix_energy
    n T (Real.sqrt (B₁ + B₂)) (Real.sqrt_nonneg _) henergy'
  have hfactor : B₁ + B₂ =
      (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
        (‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 +
          ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2) := by
    dsimp [B₁, B₂]
    rw [← mul_add]
  rw [hfactor] at hhs
  exact hhs

end NlsGge.Schur
