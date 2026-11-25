import QuantumNLS.TerraMultiRound67ExtendedSecond
import QuantumNLS.TerraMultiRound65FourthCore

/-! The fourth-moment identity with the free term expressed by the second weak
    derivative, including the case where no such L² derivative exists. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.TranslatedCorrelation QuantumNLS.WeakDerivatives
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.TerraMultiRound59RCompatibility
open QuantumNLS.TerraMultiRound59PolynomialProperty QuantumNLS.TerraMultiRound64ExtendedIdentity
open QuantumNLS.TerraMultiRound64ExtendedMeasure QuantumNLS.TerraMultiRound65FourthCore
open QuantumNLS.TerraMultiRound66WeakMap QuantumNLS.TerraMultiRound67ExtendedSecond
namespace QuantumNLS.TerraMultiRound67ExtendedIdentity
variable {L : ℝ} [Fact (0 < L)]

def secondExtended (u : Hk L 1) : ℝ≥0∞ := by
  classical
  exact if h : ∃ w, HasWeakDeriv (weakD u) w then ENNReal.ofReal (‖Classical.choose h‖^2) else ⊤

theorem freeFourth_eq_secondExtended (u : Hk L 1) : freeFourth u = secondExtended u := by
  unfold secondExtended
  split
  · rename_i h
    exact freeFourth_eq_norm u (Classical.choose_spec h)
  · rename_i h
    exact freeFourth_eq_top u h

theorem extended_fourth_identity (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) :
    RealPolynomial (Rfield (L := L) 2 (by omega) κ) ∧
    Continuous (Rfield (L := L) 2 (by omega) κ) ∧
    (∀ u : Hk L 1,
      ennrealToWithTop (∫⁻ t : ℝ, ENNReal.ofReal (t^4)
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) =
      ennrealToWithTop (secondExtended u) + ↑(Rfield (L := L) 2 (by omega) κ u)) ∧
    (∀ u : Hk L 1,
      (∫⁻ t : ℝ, ENNReal.ofReal (t^4)
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) ≠ ⊤ ↔
      ∃ w, HasWeakDeriv (weakD u) w) := by
  obtain ⟨hp, hc, hi, hf⟩ := fourth_order_core L κ hκ
  refine ⟨hp, hc, ?_, ?_⟩
  · intro u
    rw [← freeFourth_eq_secondExtended]
    exact hi u
  · intro u
    exact (hf u).trans (second_exists_iff_H2 u).symm

#print axioms freeFourth_eq_secondExtended
#print axioms extended_fourth_identity
end QuantumNLS.TerraMultiRound67ExtendedIdentity
