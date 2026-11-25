import QuantumNLS.TerraMultiRound57Tail

/-! Transfer the all-order geometric truncation estimate to a fixed-field
little-oh for any eventually selected unique small Riccati branch. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound57ScalarTail
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiExpansions
open QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.TerraMultiRound40ScalarParity
open QuantumNLS.TerraMultiRound45ScalarBound
open QuantumNLS.TerraMultiRound45TreeSum
open QuantumNLS.TerraMultiRound46Truncation
open QuantumNLS.TerraMultiRound57Tail

variable {L a : ℝ}

def scalarTail (hL : 0 < L) (ha : 1 / 2 < a) (κ : ℝ) (u : Ell2)
    (r : ℝ → Ell2) (N : ℕ) (Y : ℝ) : ℂ :=
  if hY : 0 < |Y| then
    scalar L a u (r Y) - scalar L a u (∑ n ∈ Finset.range N, treeLevel hL ha hY κ u n)
  else 0

/-- The selected branch's scalar tail is little-oh at the last retained order.
The eventual uniqueness hypothesis is exactly the one in the existing
truncation theorem; it is discharged by the small-solution theorem. -/
theorem scalar_tail_littleO (hL : 0 < L) (ha : 1 / 2 < a) (κ : ℝ) (u : Ell2)
    (r : ℝ → Ell2) (s : ℕ)
    (hu : ∀ᶠ Y : ℝ in atTop, ∀ (hY : 0 < |Y|) (t : Ell2),
      ‖t‖ ≤ 2 * ‖u‖ / |Y| → physicalT hL ha hY κ u t = t → t = r Y) :
    scalarTail hL ha κ u r (s + 1) =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * s + 1)) := by
  let B : ℝ := 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2)
  let A : ℝ := (L * physK L a ^ 2 * ‖u‖) * ‖u‖
  have hz : Tendsto (fun Y : ℝ => Y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hq : Tendsto (fun Y : ℝ => B * Y⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hz.pow 2)
  have hsmall : ∀ᶠ Y : ℝ in atTop, B * Y⁻¹ ^ 2 ≤ 1 / 2 :=
    (hq.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)).mono fun _ h => h.le
  have hpos : ∀ᶠ Y : ℝ in atTop, 0 < Y := eventually_gt_atTop 0
  have hbound : scalarTail hL ha κ u r (s + 1) =O[atTop]
      (fun Y : ℝ => A * (Y⁻¹ * (B * Y⁻¹ ^ 2) ^ (s + 1) *
        (1 - B * Y⁻¹ ^ 2)⁻¹)) := by
    apply IsBigO.of_bound'
    filter_upwards [hpos, hsmall, hu] with Y hY hs huniq
    have hY' : 0 < |Y| := abs_pos.mpr hY.ne'
    have hs' : 4 * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2) ≤ 1 / 2 := by
      simpa [B, abs_of_pos hY, mul_assoc] using hs
    have hb := scalar_tree_truncation L hL ha hY' κ u (r Y) (s + 1) hs' (huniq hY')
    have he : ‖scalarTail hL ha κ u r (s + 1) Y‖ ≤
        A * (Y⁻¹ * (B * Y⁻¹ ^ 2) ^ (s + 1) * (1 - B * Y⁻¹ ^ 2)⁻¹) := by
      simp only [scalarTail, dif_pos hY']
      rw [abs_of_pos hY] at hb
      convert hb using 1 <;> dsimp [A, B] <;> ring
    exact he.trans (le_abs_self _)
  exact hbound.trans_isLittleO (geometric_majorant_littleO A B s)

#print axioms scalar_tail_littleO
end QuantumNLS.TerraMultiRound57ScalarTail
