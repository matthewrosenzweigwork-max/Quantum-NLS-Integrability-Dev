import QuantumNLS.TerraMultiRound64InductiveLimit
import QuantumNLS.TerraMultiRound64RetainedTree
import QuantumNLS.RiccatiSobolevS

/-! Compatibility turns lower-order induction identities into the current expansion's coefficients. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RiccatiSobolevS QuantumNLS.ComplexifiedSobolevField QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound59REG007
open QuantumNLS.TerraMultiRound59SignedCharges QuantumNLS.TerraMultiRound60Kernel
open QuantumNLS.TerraMultiRound64InductiveLimit QuantumNLS.TerraMultiRound64RetainedTree
namespace QuantumNLS.TerraMultiRound64InductiveCoefficients

theorem physical_limit_from_induction (L : ℝ) [Fact (0 < L)] (n : ℕ) (hs : 2 ≤ n+1)
    (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (hu : hsq L (n : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤)
    (hμn : Integrable (fun t : ℝ => t^(2*n)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u))
    (hIH : ∀ j (hj : 2 ≤ j), j < n+1 → ∀ w : L2T L,
      hsq L (j : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤ →
      ∃ y : Ell2, ∃ hb : 0 ≤ ((j-1 : ℕ) : ℝ), fieldMap L (j-1 : ℕ) hb y = w ∧
        (∫ t : ℝ, t^(2*j) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ w)) -
        (∫ t : ℝ, t^(2*j) ∂(freeMeasure L w)) =
          retainedR (L := L) j hj κ (physicalToHk (L := L) (j-1) y) j) :
    ∃ x : Ell2, ∃ ha0 : 0 ≤ ((n : ℕ) : ℝ), fieldMap L n ha0 x = u ∧
      Tendsto (fun Y : ℝ => (∫ t, kernel (n+1) Y t ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) -
        (∫ t, kernel (n+1) Y t ∂(freeMeasure L u))) atTop
        (𝓝 (retainedR (L := L) (n+1) hs κ (physicalToHk (L := L) (n+1-1) x) (n+1))) := by
  obtain ⟨x, ha0, hx, hlim⟩ := physical_limit_from_higher_corrections L n hs κ hκ u hu hμn
  refine ⟨x, ha0, hx, hlim ?_⟩
  intro j hj hj'
  have huj : hsq L (j : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤ := by
    exact ne_top_of_le_ne_top hu (hsq_mono (by exact_mod_cast (show j ≤ n by omega)) _)
  obtain ⟨y, hb, hy, hc⟩ := hIH j hj hj' u huj
  have hvx : (physicalToHk (L := L) (n+1-1) x).val = u := by
    have hval := physicalToHk_val_eq_fieldMap L (n+1-1) (by exact_mod_cast (Nat.zero_le (n+1-1))) x
    have hx' : fieldMap L (n+1-1 : ℕ) (by exact_mod_cast (Nat.zero_le (n+1-1))) x = u := by
      simpa only [Nat.add_sub_cancel] using hx
    exact hval.trans hx'
  have hvy : (physicalToHk (L := L) (j-1) y).val = u :=
    (physicalToHk_val_eq_fieldMap L (j-1) hb y).trans hy
  have hcompat := retainedR_order (L := L) (n+1) j hs hj κ
    (physicalToHk (L := L) (n+1-1) x) (physicalToHk (L := L) (j-1) y)
    (hvx.trans hvy.symm) j (by omega) (by omega) le_rfl
  exact hc.trans hcompat.symm

#print axioms physical_limit_from_induction
end QuantumNLS.TerraMultiRound64InductiveCoefficients
