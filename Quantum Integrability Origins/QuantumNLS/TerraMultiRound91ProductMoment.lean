import QuantumNLS.TerraMultiRound91Moment
import QuantumNLS.TerraMultiRound89PhysicalCore
import QuantumNLS.ProductEnergyPreparation

/-! The first spectral moment of the actual product, on the normalized Bethe
wave basis and the physical symmetric L² carrier. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.ContactOperator QuantumNLS.ContactForm QuantumNLS.EnergyProjection
open QuantumNLS.BetheConditionalBasis QuantumNLS.BetheFreeFamily
open QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy QuantumNLS.ChargeEnergy
open QuantumNLS.ProductEnergyPreparation QuantumNLS.Ext025B3DiagonalForms
namespace QuantumNLS.TerraMultiRound91ProductMoment
variable {L : ℝ} [Fact (0 < L)]

def productForm (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) (N : ℕ) : VSym L N :=
  ⟨productH1 hu hH N, productH1_sym hu hH N⟩

theorem productForm_val (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) (N : ℕ) :
    ((valSym (productForm u hu hH N) : SymL2 L N) : L2TN L N) = prodState u N := by
  rw [valSym_val]
  exact productH1_val hu hH N

/-- The form-domain first Bethe moment is exactly the printed product energy,
with no product operator-domain assertion. -/
theorem product_first_moment (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N)
    (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) :
    let hc : 0 ≤ κ / (N : ℝ) := (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le
    ∃ b : HilbertBasis (Label N) ℂ (SymL2 L N),
      (∀ n, b n = normalizedWave L N ⟨κ / (N : ℝ), hc⟩ n) ∧
      ∃ hv : InFormDomain (energyEig L κ N) (b.repr (valSym (productForm u hu hH N))),
      ‖formRoot (energyEig L κ N) (b.repr (valSym (productForm u hu hH N))) hv‖ ^ 2 =
        N * kinetic (u : AddCircle L → ℂ) +
          2 * (κ / N) * ((Fintype.card (Pair N) : ℝ) * quartic (u : AddCircle L → ℂ)) := by
  obtain ⟨b, hmem, hb, hdense, hy, hp⟩ :=
    TerraMultiRound89PhysicalCore.physical_bethe_form_core L κ hκ N hN
  obtain ⟨hv, hm⟩ := TerraMultiRound91Moment.form_first_moment
    (div_nonneg hκ.le (Nat.cast_nonneg N)) b (energyEig L κ N) (energyEig_nonneg L κ N)
      _ hy hp hdense (productForm u hu hH N)
  refine ⟨b, hb, hv, ?_⟩
  rw [hm]
  exact hN_product hu hH κ N

#print axioms productForm_val
#print axioms product_first_moment
end QuantumNLS.TerraMultiRound91ProductMoment
