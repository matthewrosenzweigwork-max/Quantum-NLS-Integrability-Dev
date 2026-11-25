import QuantumNLS.TerraMultiRound61PhysicalFree
import QuantumNLS.TerraMultiRound59REG007

/-! REG-007 applied to the actual physical/free regularized difference. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Filter Topology Asymptotics MeasureTheory
namespace QuantumNLS.TerraMultiRound61RegularizedExpansion
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.ClassicalCharges QuantumNLS.TerraMultiRound49SobolevBridge
open QuantumNLS.TerraMultiRound59SobolevCoordinates
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RootH1RatioBounds
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.TerraMultiRound57Collection
open QuantumNLS.TerraMultiRound59SignedCharges QuantumNLS.TerraMultiRound59REG007
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound61PhysicalFree
open QuantumNLS.FreeLimit

theorem regularized_expansion (L : ℝ) [Fact (0 < L)] (s : ℕ) (hs : 2 ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (hu : hsq L (s - 1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    ∃ (x : Ell2) (ha0 : 0 ≤ ((s - 1 : ℕ) : ℝ)) (r : ℝ → Ell2),
      fieldMap L (s - 1 : ℕ) ha0 x = u ∧
      (∀ᶠ Y : ℝ in atTop,
        (∫ t, kernel 0 Y t ∂(PhysicalQuantumMeasure.measure hκ u)) -
          (∫ t, kernel 0 Y t ∂(freeMeasure L u)) =
          Y * (scalar L (s - 1 : ℕ) x (r Y) - freeScalar (L := L) (s - 1 : ℕ) x Y).re) ∧
      (fun Y : ℝ => (scalar L (s - 1 : ℕ) x (r Y) - freeScalar (L := L) (s - 1 : ℕ) x Y).re -
        ∑ j ∈ Finset.Icc 1 s, (-1 : ℝ) ^ j *
          retainedR (L := L) s hs κ (physicalToHk (L := L) (s - 1) x) j * Y⁻¹ ^ (2 * j + 1))
        =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * s + 1)) := by
  obtain ⟨_, _, _, _, _, x, ha0, r, hx, _, hr, he⟩ := REG007 L s hs κ hκ u hu
  refine ⟨x, ha0, r, hx, ?_, he⟩
  filter_upwards [hr] with Y hY
  obtain ⟨hpos, hlog, hsmall, hratio⟩ := hY
  have ha : (1 : ℝ) / 2 < ((s - 1 : ℕ) : ℝ) := by
    have hh : (1 : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ s - 1 by omega)
    linarith
  exact regularized_scalar_difference ha hpos hlog hκ u hsmall x (r Y) hx hratio

#print axioms regularized_expansion
end QuantumNLS.TerraMultiRound61RegularizedExpansion
