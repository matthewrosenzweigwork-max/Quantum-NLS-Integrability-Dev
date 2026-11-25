import QuantumNLS.TerraMultiRound45TreeTail

/-! The convergent tree series lies in the physical uniqueness ball under an
explicit large-parameter condition. Fixed-point identification is separate. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound46Radius
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.TerraMultiRound45TreeSum

/-- At geometric ratio at most one half, the tree sum is in the radius used
by the existing physical fixed-point uniqueness theorem. -/
theorem tree_sum_ball {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u : Ell2)
    (hsmall : 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2) ≤ 1 / 2) :
    ‖∑' n : ℕ, treeLevel hL ha hY κ u n‖ ≤ 2 * ‖u‖ / |Y| := by
  let q : ℝ := 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2)
  let b : ℝ := ‖u‖ * |Y|⁻¹
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqhalf : q ≤ 1 / 2 := hsmall
  have hq1 : q < 1 := by linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hg : Summable (fun n : ℕ => b * q ^ n) :=
    (summable_geometric_of_lt_one hq hq1).mul_left b
  have hbound : ∀ n : ℕ, ‖treeLevel hL ha hY κ u n‖ ≤ b * q ^ n :=
    fun n => tree_level_bound hL ha hY κ u n
  have hs : Summable (fun n : ℕ => ‖treeLevel hL ha hY κ u n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hg
  have hi : (1 - q)⁻¹ ≤ 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (show (1 : ℝ) / 2 ≤ 1 - q by linarith)
    norm_num at h
    simpa only [one_div] using h
  calc
    _ ≤ ∑' n : ℕ, ‖treeLevel hL ha hY κ u n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, b * q ^ n := hs.tsum_le_tsum hbound hg
    _ = b * (1 - q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1]
    _ ≤ b * 2 := mul_le_mul_of_nonneg_left hi hb
    _ = 2 * ‖u‖ / |Y| := by dsimp [b]; ring

#print axioms tree_sum_ball
end QuantumNLS.TerraMultiRound46Radius
