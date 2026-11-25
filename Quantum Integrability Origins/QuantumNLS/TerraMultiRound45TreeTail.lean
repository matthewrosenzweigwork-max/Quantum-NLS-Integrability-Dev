import QuantumNLS.TerraMultiRound45TreeSum

/-! Geometric tail bound for the constructed nonlinear tree series.
The identification with the Riccati fixed point remains to be proved. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound45TreeTail
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.TerraMultiRound45TreeSum

/-- After the first N tree levels, the norm of the remaining sum is bounded
by the explicit geometric tail. -/
theorem tree_tail_bound {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u : Ell2) (N : ℕ)
    (hsmall : 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2) < 1) :
    ‖∑' n : ℕ, treeLevel hL ha hY κ u (n + N)‖ ≤
      (‖u‖ * |Y|⁻¹) *
        (4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2)) ^ N *
        (1 - 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2))⁻¹ := by
  let q : ℝ := 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2)
  let b : ℝ := ‖u‖ * |Y|⁻¹
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := hsmall
  have hg : Summable (fun n : ℕ => (b * q ^ N) * q ^ n) :=
    (summable_geometric_of_lt_one hq hq1).mul_left (b * q ^ N)
  have hb : ∀ n : ℕ, ‖treeLevel hL ha hY κ u (n + N)‖ ≤ (b * q ^ N) * q ^ n := by
    intro n
    have h := tree_level_bound hL ha hY κ u (n + N)
    change ‖treeLevel hL ha hY κ u (n + N)‖ ≤ b * q ^ (n + N) at h
    simpa only [pow_add, mul_comm, mul_left_comm, mul_assoc] using h
  have hs : Summable (fun n : ℕ => ‖treeLevel hL ha hY κ u (n + N)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hg
  calc
    ‖∑' n : ℕ, treeLevel hL ha hY κ u (n + N)‖ ≤
        ∑' n : ℕ, ‖treeLevel hL ha hY κ u (n + N)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, (b * q ^ N) * q ^ n := hs.tsum_le_tsum hb hg
    _ = (b * q ^ N) * (1 - q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1]
    _ = _ := rfl

#print axioms tree_tail_bound
end QuantumNLS.TerraMultiRound45TreeTail
