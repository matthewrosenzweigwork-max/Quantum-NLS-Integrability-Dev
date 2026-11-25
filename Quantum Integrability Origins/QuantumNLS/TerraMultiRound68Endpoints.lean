import QuantumNLS.TerraMultiRound67Final
import QuantumNLS.RootIndexedMasses

/-! REG-010 partial endpoint results on the physical carrier.  This does not
assert the fractional cases or weighted continuity for positive orders. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevE1
open QuantumNLS.TranslatedCorrelation
namespace QuantumNLS.TerraMultiRound68Endpoints

/-- The zero-order mass identity, norm identity and continuity, together with
    the integer-order bare-moment equivalences and the REG-008 fourth-order
    endpoint on H¹. -/
theorem endpoint_results (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) :
    (∀ u : L2T L,
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ u Set.univ).toReal = ‖u‖^2 ∧
      Summable (fun n : ℤ => (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) ∧
      (∑' n : ℤ, (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) = ‖u‖^2 ∧
      ‖(QuantumNLS.RootIndexedMasses.masses hκ u).1‖ = ‖u‖^2) ∧
    Continuous (fun u : L2T L => QuantumNLS.RootIndexedMasses.masses hκ u) ∧
    (∀ (s : ℕ), 1 ≤ s → ∀ u : L2T L,
      (hsq L s (fun n => QuantumNLS.Fourier.coeff L u n) ≠ ⊤ ↔
        (∫⁻ t : ℝ, ENNReal.ofReal (t^(2*s)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ≠ ⊤) ∧
      ((∫⁻ t : ℝ, ENNReal.ofReal (t^(2*s)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ≠ ⊤ ↔
        (∑' n : ℤ, ENNReal.ofReal (‖QuantumNLS.RootWeightedCellsR26.momentum L n‖^(2*s) *
          (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) ≠ ⊤)) ∧
    (∀ u : Hk L 1,
      (∫⁻ t : ℝ, ENNReal.ofReal (t^4) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) ≠ ⊤ ↔
      hsq L 2 (fun n => QuantumNLS.Fourier.coeff L u.val n) ≠ ⊤) := by
  refine ⟨?_, QuantumNLS.DEF014Continuity.continuous_physical_masses hκ,
    (QuantumNLS.TerraMultiRound64REG004.REG004 L κ hκ).1, ?_⟩
  · intro u
    have h := QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ u
    refine ⟨QuantumNLS.PhysicalQuantumMeasure.full_mass hκ u, h.2.2.1, h.2.2.2.1, ?_⟩
    have hn := lp.norm_rpow_eq_tsum (p := (1 : ℝ≥0∞)) (by norm_num)
      (QuantumNLS.RootIndexedMasses.masses hκ u).1
    simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (h.2.1 _)] at hn
    exact hn.trans h.2.2.2.1
  · exact (QuantumNLS.TerraMultiRound67Final.REG008_complete L κ hκ).2.2.2.2.1

#print axioms endpoint_results
end QuantumNLS.TerraMultiRound68Endpoints
