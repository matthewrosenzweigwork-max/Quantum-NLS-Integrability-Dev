import QuantumNLS.Local001Sup

/-!
# The LOCAL-001 bounds consumed by LOCAL-005

This module packages the three successful, frozen LOCAL-001 statements as one
named structure.  The constructor below is proved from those modules; the
structure is not an axiom and does not introduce a supplied compatibility
premise.
-/

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.Local001BoundsLOCAL005

open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.LocalSpectral

/-- The three printed LOCAL-001 bounds needed by the resolvent-word estimate:
the free mode equation, the pointwise contour multiplier bound, and its
square-summable coefficient bound. -/
structure Local001PrintedBounds (L r κ : ℝ) (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) : Prop where
  freeMode : ∀ (n : ℤ) (j : Fin 2),
    (chi L n j, (pm L n : ℂ) • chi L n j) ∈ freeGraph L κ n
  multiplier : ∀ {n m : ℤ} {z : ℂ}, OnGamma L r n z →
    parity m = parity n →
    ‖freeResolventMultiplier L n z m‖ ≤ r⁻¹
  squareSum : ∀ (n : ℤ) {z : ℂ}, OnGamma L r n z →
    Summable (fun k : ℤ =>
      ‖freeResolventMultiplier L n z (sourceMode n k)‖ ^ 2) ∧
    ∑' k : ℤ,
      ‖freeResolventMultiplier L n z (sourceMode n k)‖ ^ 2 ≤
        r⁻¹ ^ 2 + 2 * ∑' k : ℕ+,
          (spacing L * (k : ℝ) - r)⁻¹ ^ 2

/-- The packaged bounds are available from the three compiled LOCAL-001
proofs, with no extra premise beyond the printed geometric hypotheses. -/
theorem local001PrintedBounds (L r κ : ℝ) (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) :
    Local001PrintedBounds L r κ hL hr hsmall := by
  refine ⟨?_, ?_, ?_⟩
  · intro n j
    exact chi_free_eigen hL κ n j
  · intro n m z hz hpar
    exact freeResolventMultiplier_norm_le hL hr hsmall hz hpar
  · intro n z hz
    exact freeResolventMultiplier_sq_summable_bound hL n hr hsmall hz

#print axioms local001PrintedBounds

end QuantumNLS.Local001BoundsLOCAL005
