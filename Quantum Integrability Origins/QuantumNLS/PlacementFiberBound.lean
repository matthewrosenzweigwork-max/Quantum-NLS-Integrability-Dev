/-
QuantumNLS.PlacementFiberBound — the source-weighted radius majorant for
the overlap-averaged product kernels in LOCAL-011.

This proves the fixed-degree overlap sum bound.  It does not identify the
ambient fiber operator with placement of the local averaged kernel.
-/
import QuantumNLS.PlacementFiberGrouping

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance QuantumNLS.PlacementGrouping
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator QuantumNLS.PlacementFiberGrouping

noncomputable section

namespace QuantumNLS.PlacementFiberBound

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem overlapCoefficient_zero_of_gt_left
    (N p q s : ℕ) (hps : p < s) :
    overlapCoefficient N p q s = 0 := by
  by_cases hsq : s ≤ q
  · simp [overlapCoefficient, hsq, Nat.choose_eq_zero_of_lt hps]
  · simp [overlapCoefficient, hsq]

/-- Restricting the source overlap probabilities to feasible intersections
does not change their total mass. Intersections larger than the left
placement have zero binomial coefficient. -/
theorem feasibleOverlapCoefficients_sum_eq_one
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N) :
    (∑ s ∈ Finset.range (min p q + 1), overlapCoefficient N p q s) = 1 := by
  have hsubset : Finset.range (min p q + 1) ⊆ Finset.range (q + 1) := by
    intro s hs
    simp only [Finset.mem_range] at hs ⊢
    omega
  have hsum :
      (∑ s ∈ Finset.range (min p q + 1), overlapCoefficient N p q s) =
        ∑ s ∈ Finset.range (q + 1), overlapCoefficient N p q s := by
    apply Finset.sum_subset hsubset
    intro s hs hnot
    have hsQ : s ≤ q := by
      have hs' := Finset.mem_range.mp hs
      omega
    have hminlt : min p q < s := by
      have hnot' : ¬ s < min p q + 1 := by
        intro hlt
        exact hnot (Finset.mem_range.mpr hlt)
      omega
    have hps : p < s := by
      by_cases hpq : p ≤ q
      · simpa [Nat.min_eq_left hpq] using hminlt
      · have hmin : min p q = q := Nat.min_eq_right (by omega)
        rw [hmin] at hminlt
        omega
    exact overlapCoefficient_zero_of_gt_left N p q s hps
  rw [hsum, sum_overlapCoefficient_eq_one hp hq]

/-- One feasible overlap-size contribution to the source radius sum. -/
def sourceWeightedOverlapTerm (N p q : ℕ) (R : ℝ)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q)
    (s : ℕ) : ℝ :=
  if hs : s ≤ min p q then (
    overlapCoefficient N p q s *
      (R ^ unionSize p q s *
        ‖averagedOverlapKernel (le_trans hs (min_le_left _ _))
          (le_trans hs (min_le_right _ _)) A B‖))
  else 0

/-- The complete source-weighted overlap sum for one pair of kernel degrees
obeys the product radius majorant. The proof sums the local averaged-kernel
bound with the exact hypergeometric overlap probabilities; no operator
compatibility premise is used. -/
theorem sourceWeightedOverlap_radius_majorant
    {N p q : ℕ} {R : ℝ} (hp : p ≤ N) (hq : q ≤ N)
    (hR : 1 ≤ R)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    (∑ s ∈ Finset.range (min p q + 1),
      sourceWeightedOverlapTerm N p q R A B s) ≤
      (R ^ p * ‖A‖) * (R ^ q * ‖B‖) := by
  classical
  let S := Finset.range (min p q + 1)
  have hbound (s : ℕ) (hs : s ∈ S) :
      sourceWeightedOverlapTerm N p q R A B s ≤
        overlapCoefficient N p q s * ((R ^ p * ‖A‖) * (R ^ q * ‖B‖)) := by
    have hsm : s ≤ min p q := by
      change s ∈ Finset.range (min p q + 1) at hs
      have hs' : s < min p q + 1 := Finset.mem_range.mp hs
      omega
    have hterm : sourceWeightedOverlapTerm N p q R A B s =
        overlapCoefficient N p q s *
          (R ^ unionSize p q s *
            ‖averagedOverlapKernel (le_trans hsm (min_le_left _ _))
              (le_trans hsm (min_le_right _ _)) A B‖) := by
      simp [sourceWeightedOverlapTerm, hsm]
    rw [hterm]
    exact weightedAveragedOverlapKernel_majorant
      (le_trans hsm (min_le_left _ _)) (le_trans hsm (min_le_right _ _)) hR A B
  calc
    _ ≤ ∑ s ∈ S,
          overlapCoefficient N p q s * ((R ^ p * ‖A‖) * (R ^ q * ‖B‖)) := by
      apply Finset.sum_le_sum
      intro s hs
      exact hbound s hs
    _ = (∑ s ∈ S, overlapCoefficient N p q s) *
          ((R ^ p * ‖A‖) * (R ^ q * ‖B‖)) := by
      rw [Finset.sum_mul]
    _ = (R ^ p * ‖A‖) * (R ^ q * ‖B‖) := by
      simp [S, feasibleOverlapCoefficients_sum_eq_one hp hq]

#print axioms QuantumNLS.PlacementFiberBound.feasibleOverlapCoefficients_sum_eq_one
#print axioms QuantumNLS.PlacementFiberBound.sourceWeightedOverlap_radius_majorant

end QuantumNLS.PlacementFiberBound
