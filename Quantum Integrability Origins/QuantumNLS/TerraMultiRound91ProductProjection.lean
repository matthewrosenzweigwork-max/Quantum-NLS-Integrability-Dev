import QuantumNLS.TerraMultiRound91ProductMoment
import QuantumNLS.TerraMultiRound89SpectralProjection

/-! Product energy-mask defect on the actual symmetric physical carrier.
The occupation-label transport and trace-distance application are separate. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.ContactOperator QuantumNLS.ContactForm QuantumNLS.EnergyProjection
open QuantumNLS.BetheConditionalBasis QuantumNLS.BetheFreeFamily
open QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy QuantumNLS.ChargeEnergy
open QuantumNLS.ProductEnergyPreparation QuantumNLS.TerraMultiRound91ProductMoment
namespace QuantumNLS.TerraMultiRound91ProductProjection
variable {L : ℝ} [Fact (0 < L)]

/-- Any actual spectral cutoff with the printed mask discards squared norm at
most the product's one-particle energy divided by E. -/
theorem product_projection_defect (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N)
    (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) (E : ℝ) (hE : 0 < E)
    (P : SymL2 L N →L[ℂ] SymL2 L N)
    (hP : ∀ n : Label N,
      P (normalizedWave L N ⟨κ / (N : ℝ), (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le⟩ n) =
        ((if energyEig L κ N n ≤ (N : ℝ) * E then (1 : ℝ) else 0 : ℝ) : ℂ) •
          normalizedWave L N ⟨κ / (N : ℝ), (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le⟩ n) :
    ‖valSym (productForm u hu hH N) - P (valSym (productForm u hu hH N))‖ ^ 2 ≤
      energyH1 κ (u : AddCircle L → ℂ) / E := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨b, hb, hv, hm⟩ := product_first_moment κ hκ N hN u hu hH
  have hPb : ∀ n, P (b n) =
      ((if energyEig L κ N n ≤ (N : ℝ) * E then (1 : ℝ) else 0 : ℝ) : ℂ) • b n := by
    intro n
    rw [hb n]
    exact hP n
  have hdef := TerraMultiRound89SpectralProjection.spectral_projection_defect b
    (energyEig L κ N) (energyEig_nonneg L κ N) ((N : ℝ) * E) (mul_pos hNr hE)
    P hPb (valSym (productForm u hu hH N)) hv
  have hen := (product_energyPrepared hu hH κ).2.2.2.2.1 hκ.le N hN
  have henergy : ‖QuantumNLS.Ext025B3DiagonalForms.formRoot (energyEig L κ N)
      (b.repr (valSym (productForm u hu hH N))) hv‖ ^ 2 ≤
      (N : ℝ) * energyH1 κ (u : AddCircle L → ℂ) := by
    rw [hm, ← hN_product hu hH κ N]
    simpa only [mul_comm] using (div_le_iff₀ hNr).mp hen
  calc
    _ ≤ ‖QuantumNLS.Ext025B3DiagonalForms.formRoot (energyEig L κ N)
      (b.repr (valSym (productForm u hu hH N))) hv‖ ^ 2 / ((N : ℝ) * E) := hdef
    _ ≤ ((N : ℝ) * energyH1 κ (u : AddCircle L → ℂ)) / ((N : ℝ) * E) :=
      div_le_div_of_nonneg_right henergy (mul_nonneg hNr.le hE.le)
    _ = _ := by field_simp

#print axioms product_projection_defect
end QuantumNLS.TerraMultiRound91ProductProjection
