import QuantumNLS.TerraMultiRound46Fixed
import QuantumNLS.TerraMultiRound45ScalarBound
import QuantumNLS.TerraMultiRound45TreeTail

/-! All-order truncation bounds for the selected Riccati branch and scalar pairing. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound46Truncation
open Finset
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc QuantumNLS.RiccatiExpansions
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.TerraMultiRound45TreeSum
open QuantumNLS.TerraMultiRound45TreeTail QuantumNLS.TerraMultiRound45ScalarBound
open QuantumNLS.TerraMultiRound46Fixed

/-- The error after the first N ordered-tree levels is bounded by their exact
geometric majorant. -/
theorem fixed_tree_truncation {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u r : Ell2) (N : ℕ)
    (hsmall : 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2) ≤ 1 / 2)
    (huniq : ∀ t : Ell2, ‖t‖ ≤ 2 * ‖u‖ / |Y| → physicalT hL ha hY κ u t = t → t = r) :
    ‖r - ∑ n ∈ range N, treeLevel hL ha hY κ u n‖ ≤
      (‖u‖ * |Y|⁻¹) *
        (4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2)) ^ N *
        (1 - 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2))⁻¹ := by
  have hlt : 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2) < 1 := by linarith
  have hs := tree_levels_summable hL ha hY κ u hlt
  have he := tree_sum_eq_unique hL ha hY κ u r hsmall huniq
  have hsplit := hs.sum_add_tsum_nat_add N
  rw [he] at hsplit
  have heq : r - ∑ n ∈ range N, treeLevel hL ha hY κ u n =
      ∑' n, treeLevel hL ha hY κ u (n + N) := by
    rw [← hsplit, add_sub_cancel_left]
  rw [heq]
  exact tree_tail_bound hL ha hY κ u N hlt

/-- The same all-order truncation bound transfers to the physical scalar pairing. -/
theorem scalar_tree_truncation (L : ℝ) (hL : 0 < L) {a Y : ℝ} (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u r : Ell2) (N : ℕ)
    (hsmall : 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2) ≤ 1 / 2)
    (huniq : ∀ t : Ell2, ‖t‖ ≤ 2 * ‖u‖ / |Y| → physicalT hL ha hY κ u t = t → t = r) :
    ‖QuantumNLS.TerraMultiRound40ScalarParity.scalar L a u r -
      QuantumNLS.TerraMultiRound40ScalarParity.scalar L a u
        (∑ n ∈ range N, treeLevel hL ha hY κ u n)‖ ≤
      (L * physK L a ^ 2 * ‖u‖) *
      ((‖u‖ * |Y|⁻¹) *
        (4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2)) ^ N *
        (1 - 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2))⁻¹) := by
  rw [← scalar_sub L hL ha]
  have hb := scalar_norm_le L hL ha u (r - ∑ n ∈ range N, treeLevel hL ha hY κ u n)
  have ht := fixed_tree_truncation hL ha hY κ u r N hsmall huniq
  have hc : 0 ≤ L * physK L a ^ 2 * ‖u‖ := by positivity
  calc
    _ ≤ L * (physK L a * ‖u‖ * (physK L a * ‖r - ∑ n ∈ range N, treeLevel hL ha hY κ u n‖)) := hb
    _ = (L * physK L a ^ 2 * ‖u‖) * ‖r - ∑ n ∈ range N, treeLevel hL ha hY κ u n‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ht hc

#print axioms fixed_tree_truncation
#print axioms scalar_tree_truncation
end QuantumNLS.TerraMultiRound46Truncation
