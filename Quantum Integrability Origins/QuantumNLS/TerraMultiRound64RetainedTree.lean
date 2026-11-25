import QuantumNLS.TerraMultiRound59SignedCharges

/-! Retained coefficients agree across Sobolev orders, via stable tree coefficients. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound64RetainedTree
open QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound57CollectedPowers
open QuantumNLS.TerraMultiRound59SobolevCoordinates QuantumNLS.TerraMultiRound59FieldOrder
open QuantumNLS.TerraMultiRound59TreeOrder QuantumNLS.TerraMultiRound59SignedCharges

variable {L : ℝ} [Fact (0 < L)]

theorem retainedR_order (s t : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t) (κ : ℝ)
    (u : Hk L (s - 1)) (v : Hk L (t - 1)) (h : u.val = v.val)
    (j : ℕ) (hj : 1 ≤ j) (hjs : j ≤ s) (hjt : j ≤ t) :
    retainedR (L := L) s hs κ u j = retainedR (L := L) t ht κ v j := by
  let x := coordinates (L := L) (s - 1) u
  let y := coordinates (L := L) (t - 1) v
  have hv : (physicalToHk (L := L) (s - 1) x).val =
      (physicalToHk (L := L) (t - 1) y).val := by
    dsimp only [x, y]
    rw [physical_coordinates, physical_coordinates]
    exact h
  have hc : treeCoefficient (L := L) (k := s - 1) κ x s (2*j+1) =
      treeCoefficient (L := L) (k := t - 1) κ y t (2*j+1) := by
    calc
      _ = treeCoefficient (L := L) (k := s - 1) κ x j (2*j+1) :=
        (tree_coefficient_truncation_stable κ x j s (2*j+1) hjs le_rfl).symm
      _ = treeCoefficient (L := L) (k := t - 1) κ y j (2*j+1) :=
        tree_coeff_order κ x y j (2*j+1) hv
      _ = _ := tree_coefficient_truncation_stable κ y j t (2*j+1) hjt le_rfl
  have h1 := odd_coefficient_signed (L := L) s hs κ x j hj hjs
  have h2 := odd_coefficient_signed (L := L) t ht κ y j hj hjt
  dsimp only [x, y] at h1 h2
  rw [physical_coordinates] at h1 h2
  change treeCoefficient (L := L) (k := s - 1) κ x s (2*j+1) =
    treeCoefficient (L := L) (k := t - 1) κ y t (2*j+1) at hc
  dsimp only [x, y] at hc
  rw [hc] at h1
  exact (mul_left_cancel₀ (pow_ne_zero j (by norm_num : (-1 : ℝ) ≠ 0))) (h1.symm.trans h2)

#print axioms retainedR_order
end QuantumNLS.TerraMultiRound64RetainedTree
