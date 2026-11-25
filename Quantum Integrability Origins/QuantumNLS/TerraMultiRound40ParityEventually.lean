import QuantumNLS.TerraMultiRound40ScalarParity

/-! The logarithm-disk condition follows from the signed fixed-point bounds
for sufficiently large absolute parameter. -/
set_option autoImplicit false
noncomputable section
open Complex ComplexConjugate
namespace QuantumNLS.TerraMultiRound40ParityEventually
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiPointwiseDisc QuantumNLS.RiccatiExpansions
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.TerraMultiRound40ScalarParity

/-- A single embedding constant controls the physical representative. -/
theorem representative_bound {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) :
    ∃ D : ℝ, 0 < D ∧ ∀ (x : Ell2) (t : ℝ), ‖physRep L a x t‖ ≤ D * ‖x‖ := by
  let D := max 1 ((Real.sqrt L)⁻¹ * ((1 + ∑' k : ℤ, (wt L a k)⁻¹) / 2))
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨D, hD, ?_⟩
  intro x t
  calc ‖physRep L a x t‖
      ≤ (Real.sqrt L)⁻¹ * ∑' k, ‖toField L a x k‖ := physRep_sup_bound hL ha x t
    _ ≤ (Real.sqrt L)⁻¹ * (((1 + ∑' k : ℤ, (wt L a k)⁻¹) / 2) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (l1_le_norm hL ha x) (inv_nonneg.mpr (Real.sqrt_nonneg L))
    _ = ((Real.sqrt L)⁻¹ * ((1 + ∑' k : ℤ, (wt L a k)⁻¹) / 2)) * ‖x‖ := by ring
    _ ≤ D * ‖x‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg x)

/-- Existence of opposite signed fixed points and their scalar parity for all
sufficiently large absolute parameters. -/
theorem scalar_parity_eventually (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ}
    (ha : 1 / 2 < a) (κ : ℝ) (hκ : κ ≠ 0) (u : Ell2) :
    ∃ B : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ |Y| →
      ∃ (hY : 0 < |Y|) (r s : Ell2),
        ‖r‖ ≤ 2 * ‖u‖ / |Y| ∧ ‖s‖ ≤ 2 * ‖u‖ / |Y| ∧
        physicalT hLf.out ha hY κ u r = r ∧
        physicalT hLf.out ha (by simpa using hY : 0 < |-Y|) κ u s = s ∧
        scalar L a u r = -conj (scalar L a u s) := by
  obtain ⟨D, hD, hbound⟩ := representative_bound hLf.out ha
  obtain ⟨B₀, hB₀, hfix⟩ := physical_fixed_eventually hLf.out ha κ u
  let C : ℝ := 4 * |κ| * D ^ 2 * ‖u‖ ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨max B₀ (C + 1), lt_of_lt_of_le hB₀ (le_max_left _ _), ?_⟩
  intro Y hYB
  have hY : 0 < |Y| := lt_of_lt_of_le hB₀ ((le_max_left _ _).trans hYB)
  obtain ⟨_, r, hr, hfr, _⟩ := hfix Y ((le_max_left _ _).trans hYB)
  obtain ⟨_, s, hs, hfs, _⟩ := hfix (-Y) (by simpa using (le_max_left B₀ (C + 1)).trans hYB)
  have hs' : ‖s‖ ≤ 2 * ‖u‖ / |Y| := by simpa using hs
  refine ⟨hY, r, s, hr, hs', hfr, hfs, ?_⟩
  apply scalar_parity_of_small_product L ha hY hκ u r s hfr hfs
  intro x
  have hR : ‖physRep L a r x‖ ≤ D * (2 * ‖u‖ / |Y|) :=
    (hbound r x).trans (mul_le_mul_of_nonneg_left hr hD.le)
  have hS : ‖physRep L a s x‖ ≤ D * (2 * ‖u‖ / |Y|) :=
    (hbound s x).trans (mul_le_mul_of_nonneg_left hs' hD.le)
  have hT : 0 ≤ D * (2 * ‖u‖ / |Y|) := by positivity
  have hprod : ‖(κ : ℂ) * physRep L a r x * conj (physRep L a s x)‖ ≤
      |κ| * (D * (2 * ‖u‖ / |Y|)) ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_conj]
    have hmul := mul_le_mul hR hS (norm_nonneg _) hT
    calc |κ| * ‖physRep L a r x‖ * ‖physRep L a s x‖
        = |κ| * (‖physRep L a r x‖ * ‖physRep L a s x‖) := by ring
      _ ≤ |κ| * ((D * (2 * ‖u‖ / |Y|)) * (D * (2 * ‖u‖ / |Y|))) :=
        mul_le_mul_of_nonneg_left hmul (abs_nonneg κ)
      _ = _ := by ring
  have hYlarge : C + 1 ≤ |Y| := (le_max_right _ _).trans hYB
  have hsquare : C < |Y| ^ 2 := by nlinarith [sq_nonneg (|Y| - 1)]
  have hratio : |κ| * (D * (2 * ‖u‖ / |Y|)) ^ 2 = C / |Y| ^ 2 := by
    dsimp [C]
    field_simp
    ring
  rw [hratio] at hprod
  exact hprod.trans_lt ((div_lt_one (sq_pos_of_pos hY)).2 hsquare)

end QuantumNLS.TerraMultiRound40ParityEventually
#print axioms QuantumNLS.TerraMultiRound40ParityEventually.representative_bound
#print axioms QuantumNLS.TerraMultiRound40ParityEventually.scalar_parity_eventually
