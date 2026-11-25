import NlsGge.Schur.FreeResolventDVDMatrixCrossEnergy
import NlsGge.Schur.FreeResolventDVDMatrixSameChannelZero
import NlsGge.Schur.FreeResolventDVDMatrixReindex

set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

private def dvdMatrixEntryENN (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (input output : Bool × Sector n) : ℝ≥0∞ :=
  ENNReal.ofReal
    (‖inner ℂ (parityPairVector n output)
      (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n input))‖ ^ 2)

/-- The whole actual DVD matrix energy is the sum of the two independently
quantified off-diagonal potential energies; its same-parity entries vanish. -/
theorem freeResolventDVD_matrix_energy_eq_cross_from_reindex
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    (∑' input : Bool × Sector n, ∑' output : Bool × Sector n,
      ENNReal.ofReal
        (‖inner ℂ (parityPairVector n output)
          (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
            (parityPairVector n input))‖ ^ 2)) =
      (∑' ml : Sector n × Sector n,
        ENNReal.ofReal
          (‖inner ℂ (parityPairVector n (true, ml.1))
            (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
              (parityPairVector n (false, ml.2)))‖ ^ 2)) +
      (∑' ml : Sector n × Sector n,
        ENNReal.ofReal
          (‖inner ℂ (parityPairVector n (false, ml.1))
            (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
              (parityPairVector n (true, ml.2)))‖ ^ 2)) := by
  let f : Bool × Bool → Sector n × Sector n → ℝ≥0∞ := fun bc q =>
    dvdMatrixEntryENN u₁ u₂ hu₁ hu₂ n z hz (bc.1, q.2) (bc.2, q.1)
  have hTT : ∀ q, f (true, true) q = 0 := by
    intro q
    simp only [f]
    exact ENNReal.ofReal_eq_zero.mpr (by
      rw [NlsGge.Schur.freeResolventPotentialFreeResolvent_true_true_entry_zero
        u₁ u₂ hu₁ hu₂ n z hz q.1 q.2]
      simp)
  have hFF : ∀ q, f (false, false) q = 0 := by
    intro q
    simp only [f]
    exact ENNReal.ofReal_eq_zero.mpr (by
      rw [NlsGge.Schur.freeResolventPotentialFreeResolvent_false_false_entry_zero
        u₁ u₂ hu₁ hu₂ n z hz q.1 q.2]
      simp)
  calc
    (∑' input : Bool × Sector n, ∑' output : Bool × Sector n,
      ENNReal.ofReal
        (‖inner ℂ (parityPairVector n output)
          (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
            (parityPairVector n input))‖ ^ 2)) =
      (∑' input : Bool × Sector n, ∑' output : Bool × Sector n,
        f (input.1, output.1) (output.2, input.2)) := by
          rfl
    _ = (∑' q : Sector n × Sector n, f (true, false) q) +
        (∑' q : Sector n × Sector n, f (false, true) q) :=
      ENNReal_tsum_dvd_pair_reindex_offdiag f hTT hFF
    _ = _ := by
      simp only [f, dvdMatrixEntryENN]
      rw [add_comm]

end NlsGge.Schur
