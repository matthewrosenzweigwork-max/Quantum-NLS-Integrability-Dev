import QuantumNLS.Reg014Continuity
import QuantumNLS.TerraMultiRound73TailConvergence

/-! Bounded positive moment truncations of the actual physical measure. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped Topology BoundedContinuousFunction
open QuantumNLS.PhysicalTensor
namespace QuantumNLS.TerraMultiRound73Truncation

/-- The bounded continuous test `min (|t|^p) B`, for nonnegative exponent
and cutoff. -/
def truncation (p B : ℝ) (hp : 0 ≤ p) (hB : 0 ≤ B) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun t : ℝ => min (|t| ^ p) B,
      (continuous_abs.rpow_const (fun _ => Or.inr hp)).min continuous_const⟩ B (by
        intro x y
        have hx : 0 ≤ min (|x| ^ p) B := le_min (Real.rpow_nonneg (abs_nonneg x) p) hB
        have hy : 0 ≤ min (|y| ^ p) B := le_min (Real.rpow_nonneg (abs_nonneg y) p) hB
        have hxB : min (|x| ^ p) B ≤ B := min_le_right _ _
        have hyB : min (|y| ^ p) B ≤ B := min_le_right _ _
        change dist (min (|x| ^ p) B) (min (|y| ^ p) B) ≤ B
        rw [Real.dist_eq, abs_le]
        constructor <;> linarith)

/-- Every bounded truncation of a physical moment is continuous in L².
No moment finiteness is required for the untruncated power. -/
theorem continuous_physical_truncation {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (p B : ℝ) (hp : 0 ≤ p) (hB : 0 ≤ B) :
    Continuous (fun u : L2T L => ∫ t : ℝ, min (|t| ^ p) B
      ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) := by
  have h := QuantumNLS.Reg014Continuity.integral_Mmeas_continuous (L := L) κ hκ.le
    (truncation p B hp hB)
  convert h using 1
  funext u
  rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas]
  rfl

#print axioms truncation
#print axioms continuous_physical_truncation
end QuantumNLS.TerraMultiRound73Truncation
