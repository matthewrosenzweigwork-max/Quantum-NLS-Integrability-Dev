import QuantumNLS.TerraMultiRound39PhysicalBall
import QuantumNLS.RiccatiChargeIdent

/-! An explicit equivalent algebra norm for the physical Fourier model and
its exact-radius fixed-point specialization. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound39AlgebraBall
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.TerraMultiRound39PhysicalBall

def algebraScale (L a : ℝ) : ℝ := max 1 (Cmul L a / Real.sqrt L)
def algebraNorm (L a : ℝ) (x : Ell2) : ℝ := algebraScale L a * ‖x‖

def physicalProduct {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) : Ell2 :=
  (((Real.sqrt L)⁻¹ : ℝ) : ℂ) • mulBil hL ha x y

theorem algebraScale_pos (L a : ℝ) : 0 < algebraScale L a :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- The model product is exactly pointwise multiplication of physical representatives. -/
theorem physicalProduct_rep {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (x y : Ell2) (t : ℝ) :
    QuantumNLS.RiccatiPointwiseDisc.physRep L a (physicalProduct hL ha x y) t =
      QuantumNLS.RiccatiPointwiseDisc.physRep L a x t *
        QuantumNLS.RiccatiPointwiseDisc.physRep L a y t := by
  have hs : ((Real.sqrt L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hL).ne'
  simp only [physicalProduct, QuantumNLS.RiccatiExpansions.physRep_smul,
    Pi.smul_apply, smul_eq_mul, mulBil_apply, QuantumNLS.RiccatiChargeIdent.physRep_mulEll]
  rw [Complex.ofReal_inv]
  simp only [← mul_assoc, inv_mul_cancel₀ hs, one_mul]

/-- Physical multiplication is submultiplicative for the rescaled norm. -/
theorem algebraNorm_product {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) :
    algebraNorm L a (physicalProduct hL ha x y) ≤ algebraNorm L a x * algebraNorm L a y := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hC : 0 ≤ Cmul L a := Real.sqrt_nonneg _
  have hbound : ‖physicalProduct hL ha x y‖ ≤
      (Cmul L a / Real.sqrt L) * ‖x‖ * ‖y‖ := by
    unfold physicalProduct
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
    calc (Real.sqrt L)⁻¹ * ‖mulBil hL ha x y‖
        ≤ (Real.sqrt L)⁻¹ * (Cmul L a * ‖x‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left (norm_mulBil_le hL ha x y) (inv_nonneg.mpr hs.le)
      _ = (Cmul L a / Real.sqrt L) * ‖x‖ * ‖y‖ := by ring
  have hscale : Cmul L a / Real.sqrt L ≤ algebraScale L a := le_max_right _ _
  have hs0 : 0 ≤ algebraScale L a := (algebraScale_pos L a).le
  have hxy : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg x) (norm_nonneg y)
  unfold algebraNorm
  calc algebraScale L a * ‖physicalProduct hL ha x y‖
      ≤ algebraScale L a * ((Cmul L a / Real.sqrt L) * ‖x‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left hbound hs0
    _ ≤ algebraScale L a * (algebraScale L a * ‖x‖ * ‖y‖) := by gcongr
    _ = (algebraScale L a * ‖x‖) * (algebraScale L a * ‖y‖) := by ring

/-- The same fixed point and uniqueness hold in the explicit equivalent algebra norm. -/
theorem algebra_fixed_eventually {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (κ : ℝ) (u : Ell2) :
    ∃ B : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ |Y| →
      ∃ (hY : 0 < |Y|) (r : Ell2),
        algebraNorm L a r ≤ 2 * algebraNorm L a u / |Y| ∧
        physicalT hL ha hY κ u r = r ∧
        ∀ r' : Ell2, algebraNorm L a r' ≤ 2 * algebraNorm L a u / |Y| →
          physicalT hL ha hY κ u r' = r' → r' = r := by
  obtain ⟨B, hB, he⟩ := physical_fixed_eventually hL ha κ u
  refine ⟨B, hB, ?_⟩
  intro Y hYB
  obtain ⟨hY, r, hr, hf, huniq⟩ := he Y hYB
  have hc := algebraScale_pos L a
  have eqn (x : Ell2) : 2 * algebraNorm L a x / |Y| =
      algebraScale L a * (2 * ‖x‖ / |Y|) := by unfold algebraNorm; ring
  refine ⟨hY, r, ?_, hf, ?_⟩
  · rw [eqn]
    exact mul_le_mul_of_nonneg_left hr hc.le
  · intro r' hr' hfix
    apply huniq r' _ hfix
    rw [eqn] at hr'
    change algebraScale L a * ‖r'‖ ≤ _ at hr'
    exact le_of_mul_le_mul_left hr' hc

end QuantumNLS.TerraMultiRound39AlgebraBall
#print axioms QuantumNLS.TerraMultiRound39AlgebraBall.physicalProduct_rep
#print axioms QuantumNLS.TerraMultiRound39AlgebraBall.algebraNorm_product
#print axioms QuantumNLS.TerraMultiRound39AlgebraBall.algebra_fixed_eventually
