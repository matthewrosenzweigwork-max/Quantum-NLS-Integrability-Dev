import QuantumNLS.TerraMultiRound24FreeBasis

/-! The free-basis embedding intertwines the two source symmetries. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace QuantumNLS.LocalSpectral.Round24
open Round23

/-- Swap-conjugation commutes with the actual free embedding. -/
theorem embed_swap (L : ℝ) (n : ℤ) (v : E2) :
    liftFiber L swapConjIsometry (embed L n v) = embed L n (swapConj v) := by
  rw [embed_apply, embed_apply]
  change (swapConjIsometry.toContinuousLinearMap.compLpₗ 2 (μI L))
      (v 0 • chi L n 0 + v 1 • chi L n 1) = _
  rw [map_add]
  change liftFiber L swapConjIsometry (v 0 • chi L n 0) +
    liftFiber L swapConjIsometry (v 1 • chi L n 1) = _
  rw [liftFiber_swap_smul, liftFiber_swap_smul, swap_chi_zero, swap_chi_one]
  simp [swapConj, vec2, add_comm]

/-- The component sign flip commutes with the actual free embedding. -/
theorem embed_parity (L : ℝ) (n : ℤ) (v : E2) :
    liftFiber L parityFlipIsometry (embed L n v) = embed L n (parityFlip v) := by
  rw [embed_apply, embed_apply]
  change (parityFlipIsometry.toContinuousLinearMap.compLpₗ 2 (μI L))
      (v 0 • chi L n 0 + v 1 • chi L n 1) = _
  rw [map_add]
  change liftFiber L parityFlipIsometry (v 0 • chi L n 0) +
    liftFiber L parityFlipIsometry (v 1 • chi L n 1) = _
  rw [liftFiber_parity_smul, liftFiber_parity_smul, parity_chi_zero, parity_chi_one]
  simp [parityFlip, Jm, smul_neg]

end QuantumNLS.LocalSpectral.Round24
#print axioms QuantumNLS.LocalSpectral.Round24.embed_swap
#print axioms QuantumNLS.LocalSpectral.Round24.embed_parity
