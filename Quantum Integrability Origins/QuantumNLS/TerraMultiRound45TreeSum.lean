import QuantumNLS.TerraMultiRound45Trees

/-! Catalan majorant and absolute convergence for ordered Riccati trees.
Identification of the sum with the fixed point is a separate step. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound45TreeSum
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.TerraMultiRound45Trees

/-- Sum the ordered binary trees with the prescribed number of nonlinear vertices. -/
def treeLevel {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (hY : 0 < |Y|)
    (κ : ℝ) (u : Ell2) (n : ℕ) : Ell2 :=
  ∑ t ∈ BinaryTree.treesOfNumNodesEq n, treeTerm hL ha hY κ u t

/-- The Catalan count is bounded by 4^n. -/
theorem catalan_le_four_pow (n : ℕ) : catalan n ≤ 4 ^ n := by
  rw [catalan_eq_centralBinom_div]
  exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow n)

/-- All trees at one level obey the geometric majorant. -/
theorem tree_level_bound {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u : Ell2) (n : ℕ) :
    ‖treeLevel hL ha hY κ u n‖ ≤
      (‖u‖ * |Y|⁻¹) *
        (4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2)) ^ n := by
  let q : ℝ := |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2
  let b : ℝ := ‖u‖ * |Y|⁻¹
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hc : (catalan n : ℝ) ≤ (4 : ℝ) ^ n := by exact_mod_cast catalan_le_four_pow n
  change ‖treeLevel hL ha hY κ u n‖ ≤ b * (4 * q) ^ n
  calc
    _ ≤ ∑ t ∈ BinaryTree.treesOfNumNodesEq n, ‖treeTerm hL ha hY κ u t‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ _t ∈ BinaryTree.treesOfNumNodesEq n, b * q ^ n := by
      apply Finset.sum_le_sum
      intro t ht
      have h := tree_term_bound hL ha hY κ u t
      have ht' : t.numNodes = n := BinaryTree.mem_treesOfNumNodesEq.mp ht
      simpa only [ht', b, q] using h
    _ = (catalan n : ℝ) * (b * q ^ n) := by
      simp [BinaryTree.treesOfNumNodesEq_card_eq_catalan]
    _ ≤ (4 : ℝ) ^ n * (b * q ^ n) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hb (pow_nonneg hq _))
    _ = b * (4 * q) ^ n := by rw [mul_pow]; ring

/-- The full series of ordered tree levels converges absolutely whenever the
explicit geometric ratio is below one. -/
theorem tree_levels_summable {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u : Ell2)
    (hsmall : 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2) < 1) :
    Summable (treeLevel hL ha hY κ u) := by
  have hq : 0 ≤ 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2) := by positivity
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hq hsmall).mul_left (‖u‖ * |Y|⁻¹)) ?_
  exact fun n => tree_level_bound hL ha hY κ u n

#print axioms catalan_le_four_pow
#print axioms tree_level_bound
#print axioms tree_levels_summable
end QuantumNLS.TerraMultiRound45TreeSum
