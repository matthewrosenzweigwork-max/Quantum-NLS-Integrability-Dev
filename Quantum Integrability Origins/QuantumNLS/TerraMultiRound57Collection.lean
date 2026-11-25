import QuantumNLS.TerraMultiRound57LevelIdentity
import QuantumNLS.TerraMultiRound57ScalarTail

/-! Assemble the small-branch tail with the finite tree-level remainders,
keeping the zero level as the exact free-resolvent scalar. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound57Collection
open QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.TerraMultiRound38SignedPicard
open QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.TerraMultiRound40ScalarParity
open QuantumNLS.TerraMultiRound45TreeSum
open QuantumNLS.TerraMultiRound56FiniteRemainder
open QuantumNLS.TerraMultiRound56LevelCollection
open QuantumNLS.TerraMultiRound57LevelIdentity
open QuantumNLS.TerraMultiRound57ScalarTail

variable {L : ℝ} [Fact (0 < L)]

def freeScalar (a : ℝ) (u : Ell2) (Y : ℝ) : ℂ :=
  if hY : 0 < |Y| then scalar L a u (signedCLM L Y hY u) else 0

/-- Finite correlation coefficients and the exact free term approximate any
eventually unique small branch, with the fixed-field little-oh remainder. -/
theorem scalar_tree_expansion (s : ℕ) (hs : 2 ≤ s) (κ : ℝ) (u : Ell2)
    (r : ℝ → Ell2)
    (hu : ∀ᶠ Y : ℝ in atTop, ∀ (hY : 0 < |Y|) (t : Ell2),
      ‖t‖ ≤ 2 * ‖u‖ / |Y| → physicalT (Fact.out : 0 < L)
        (a := ((s - 1 : ℕ) : ℝ)) (by
          have h : (1 : ℝ) ≤ (s - 1 : ℕ) := by exact_mod_cast (show 1 ≤ s - 1 by omega)
          linarith) hY κ u t = t → t = r Y) :
    (fun Y : ℝ => scalar L (s - 1 : ℕ) u (r Y) -
      (freeScalar (L := L) (s - 1 : ℕ) u Y +
        (∑ n ∈ Finset.Ico 1 s, positiveApprox (L := L) (k := s - 1) κ u n (2 * (s - n) - 1) Y) +
        leadingApprox (L := L) (k := s - 1) κ u s Y))
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * s + 1)) := by
  have hk : 1 ≤ s - 1 := by omega
  have ha : (1 : ℝ) / 2 < ((s - 1 : ℕ) : ℝ) := by
    have h : (1 : ℝ) ≤ (s - 1 : ℕ) := by exact_mod_cast hk
    linarith
  have ht := scalar_tail_littleO (Fact.out : 0 < L) ha κ u r s hu
  have hf := finite_tree_remainders (L := L) s hs κ u
  have hsum := ht.add hf
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  have hY' : 0 < |Y| := abs_pos.mpr hY.ne'
  let f : ℕ → ℂ := fun n => scalar L (s - 1 : ℕ) u
    (treeLevel (Fact.out : 0 < L) ha hY' κ u n)
  have hsplit : (∑ n ∈ Finset.range (s + 1), f n) = f 0 + (∑ n ∈ Finset.Ico 1 s, f n) + f s := by
    rw [Finset.sum_range_succ, ← Finset.sum_range_add_sum_Ico f (show 1 ≤ s by omega)]
    simp
  simp only [scalarTail, dif_pos hY', freeScalar]
  rw [scalar_sum L (Fact.out : 0 < L) ha, hsplit]
  dsimp only [f]
  rw [scalar_level_zero ha hY' κ u]
  simp_rw [positive_level_identity (L := L) hk Y hY' κ u,
    leading_level_identity (L := L) hk Y hY' κ u]
  rw [Finset.sum_sub_distrib]
  abel
  exact Filter.Eventually.of_forall (fun _ => rfl)

#print axioms scalar_tree_expansion
end QuantumNLS.TerraMultiRound57Collection
