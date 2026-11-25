import QuantumNLS.TerraMultiRound46Cauchy
import QuantumNLS.TerraMultiRound46Radius

/-! Identification of the tree series as the physical Riccati fixed point. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound46Fixed
open Finset
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.TerraMultiRound38SignedPicard QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.TerraMultiRound45TreeSum QuantumNLS.TerraMultiRound46Root
open QuantumNLS.TerraMultiRound46Recursion QuantumNLS.TerraMultiRound46Cauchy
open QuantumNLS.TerraMultiRound46Radius

/-- Bundled form of the physical two-input branch operation. -/
def branchCLM {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u : Ell2) : Ell2 →L[ℂ] Ell2 →L[ℂ] Ell2 :=
  -((κ / L : ℂ) •
    ((ContinuousLinearMap.compL ℂ Ell2 Ell2 Ell2
      ((signedCLM L Y hY).comp (mulBil hL ha (jEll u)))).comp (mulBil hL ha)))

theorem branchCLM_apply {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u x y : Ell2) :
    branchCLM hL ha hY κ u x y = branch hL ha hY κ u x y := by
  simp [branchCLM, branch, ContinuousLinearMap.compL_apply]

/-- The absolutely convergent ordered-tree sum solves the actual physical
Riccati fixed point equation. -/
theorem tree_sum_fixed {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u : Ell2)
    (hsmall : 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2) < 1) :
    physicalT hL ha hY κ u (∑' n, treeLevel hL ha hY κ u n) =
      ∑' n, treeLevel hL ha hY κ u n := by
  let f := treeLevel hL ha hY κ u
  let q : ℝ := 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hg := (summable_geometric_of_lt_one hq hsmall).mul_left (‖u‖ * |Y|⁻¹)
  have hn : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => tree_level_bound hL ha hY κ u n) hg
  have hc := bilinear_cauchy (branchCLM hL ha hY κ u) f f hn hn
  simp only [branchCLM_apply] at hc
  dsimp [f] at hc
  simp only [← tree_level_succ] at hc
  have hs := hn.of_norm
  have he := hs.tsum_eq_zero_add
  change (∑' n, f n) = f 0 + ∑' n, f (n + 1) at he
  dsimp [f] at he
  rw [tree_level_zero] at he
  simp only [physicalT, signedT, sub_eq_add_neg, Complex.ofReal_div]
  change signedCLM L Y hY u + branch hL ha hY κ u (∑' n, f n) (∑' n, f n) = ∑' n, f n
  rw [hc]
  exact he.symm

/-- Any fixed point in the existing uniqueness ball is exactly the tree sum. -/
theorem tree_sum_eq_unique {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u r : Ell2)
    (hsmall : 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2) ≤ 1 / 2)
    (huniq : ∀ t : Ell2, ‖t‖ ≤ 2 * ‖u‖ / |Y| → physicalT hL ha hY κ u t = t → t = r) :
    (∑' n, treeLevel hL ha hY κ u n) = r := by
  apply huniq
  · exact tree_sum_ball hL ha hY κ u hsmall
  · exact tree_sum_fixed hL ha hY κ u (by linarith)

#print axioms branchCLM_apply
#print axioms tree_sum_fixed
#print axioms tree_sum_eq_unique
end QuantumNLS.TerraMultiRound46Fixed
