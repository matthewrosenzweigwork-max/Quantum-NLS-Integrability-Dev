import QuantumNLS.TerraMultiRound26InvSqrt

/-! The sign flip is unitary on the interval space and on the free fiber. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace QuantumNLS.LocalSpectral.Round26
open Round23 Round24 Round25

/-- A pointwise involutive isometry lifts to an involution of the L² space. -/
theorem liftFiber_involution (L : ℝ) (T : E2 →ₗᵢ[ℝ] E2)
    (hT : ∀ v, T (T v) = v) (x : H2 L) :
    liftFiber L T (liftFiber L T x) = x := by
  rw [Lp.ext_iff]
  filter_upwards [T.toContinuousLinearMap.coeFn_compLp (liftFiber L T x),
    T.toContinuousLinearMap.coeFn_compLp x] with t ht hs
  change (T.toContinuousLinearMap.compLp (liftFiber L T x)) t = x t
  rw [ht]
  change T ((T.toContinuousLinearMap.compLp x) t) = x t
  rw [hs]
  exact hT (x t)

/-- Every such lift preserves the L² norm. -/
theorem liftFiber_norm (L : ℝ) (T : E2 →ₗᵢ[ℝ] E2)
    (hT : ∀ v, T (T v) = v) (x : H2 L) : ‖liftFiber L T x‖ = ‖x‖ := by
  have bound (y : H2 L) : ‖liftFiber L T y‖ ≤ ‖y‖ := by
    simpa [liftFiber] using T.toContinuousLinearMap.norm_compLp_le y
  apply le_antisymm (bound x)
  simpa [liftFiber_involution L T hT x] using bound (liftFiber L T x)

/-- The actual interval sign flip is a complex-linear isometry. -/
def parityL2Isometry (L : ℝ) : H2 L →ₗᵢ[ℂ] H2 L where
  toLinearMap := (parityOp L).toLinearMap
  norm_map' x := liftFiber_norm L parityFlipIsometry parityFlip_involutive x

/-- Its action twice is the identity. -/
theorem parityOp_involution (L : ℝ) (x : H2 L) : parityOp L (parityOp L x) = x :=
  liftFiber_involution L parityFlipIsometry parityFlip_involutive x

/-- The sign flip preserves the complex inner product on the interval space. -/
theorem parityOp_inner (L : ℝ) (x y : H2 L) :
    ⟪parityOp L x, parityOp L y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (parityL2Isometry L).inner_map_map x y

end QuantumNLS.LocalSpectral.Round26
#print axioms QuantumNLS.LocalSpectral.Round26.liftFiber_involution
#print axioms QuantumNLS.LocalSpectral.Round26.liftFiber_norm
#print axioms QuantumNLS.LocalSpectral.Round26.parityL2Isometry
#print axioms QuantumNLS.LocalSpectral.Round26.parityOp_involution
#print axioms QuantumNLS.LocalSpectral.Round26.parityOp_inner
