import QuantumNLS.ResolventWordCoefficientLOCAL005

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace QuantumNLS.ResolventWordEstimateStage2LOCAL005

open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.Local001BoundsLOCAL005

/-- The printed `ℓ²` norm of one independent Fourier input. -/
def inputL2Norm {k : ℕ} (u : Fin k → ℤ → ℂ) (j : Fin k) : ℝ :=
  Real.sqrt (∑' m : ℤ, ‖u j m‖ ^ 2)

/-- The square of the input norm is its defining nonnegative series. -/
theorem inputL2Norm_sq {k : ℕ} (u : Fin k → ℤ → ℂ) (j : Fin k) :
    inputL2Norm u j ^ 2 = ∑' m : ℤ, ‖u j m‖ ^ 2 := by
  unfold inputL2Norm
  rw [Real.sq_sqrt]
  exact tsum_nonneg fun m => sq_nonneg ‖u j m‖

/-- Project the square-summable multiplier estimate from the proved
LOCAL-001 package at each output mode and contour point. -/
theorem multiplier_square_data (L r κ : ℝ) (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2)
    (hLOCAL001 : Local001PrintedBounds L r κ hL hr hsmall)
    (n : ℤ) {z : ℂ} (hz : OnGamma L r n z) :
    Summable (fun m : ℤ =>
        ‖freeResolventMultiplier L n z (sourceMode n m)‖ ^ 2) ∧
      ∑' m : ℤ, ‖freeResolventMultiplier L n z (sourceMode n m)‖ ^ 2 ≤
        r⁻¹ ^ 2 + 2 * ∑' j : ℕ+,
          (spacing L * (j : ℝ) - r)⁻¹ ^ 2 := by
  exact hLOCAL001.squareSum n hz

#print axioms inputL2Norm_sq
#print axioms multiplier_square_data

end QuantumNLS.ResolventWordEstimateStage2LOCAL005
