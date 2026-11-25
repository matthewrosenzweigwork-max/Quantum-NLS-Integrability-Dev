import QuantumNLS.TerraMultiRound67Identify
import QuantumNLS.TerraMultiRound67ExtendedIdentity

/-! REG-008: explicit fourth moment, including the extended free term. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.TranslatedCorrelation QuantumNLS.WeakDerivatives QuantumNLS.RiccatiSobolevE1
open QuantumNLS.TerraMultiRound59RCompatibility QuantumNLS.TerraMultiRound59PolynomialProperty
open QuantumNLS.TerraMultiRound64ExtendedMeasure QuantumNLS.TerraMultiRound65FourthCore
open QuantumNLS.TerraMultiRound66WeakMap QuantumNLS.TerraMultiRound67ExtendedSecond
open QuantumNLS.TerraMultiRound67ExtendedIdentity QuantumNLS.TerraMultiRound67Quartic
open QuantumNLS.TerraMultiRound67DensityCandidate QuantumNLS.TerraMultiRound67DensityExtension
open QuantumNLS.TerraMultiRound67DensityRule QuantumNLS.TerraMultiRound67Sextic
open QuantumNLS.TerraMultiRound67Correction QuantumNLS.TerraMultiRound67Identify
open QuantumNLS.RootH1RatioOperator
namespace QuantumNLS.TerraMultiRound67REG008
variable {L : ℝ} [Fact (0 < L)]

theorem correction_printed (κ : ℝ) (u : Hk L 1) :
    correction κ u = κ * (∫ x : AddCircle L,
      6 * (‖contRep (by omega) u x‖^2 * ‖(weakD u : AddCircle L → ℂ) x‖^2) +
      ‖(densityCandidate u : AddCircle L → ℂ) x‖^2 ∂volume) +
      2 * κ^2 * ∫ x : AddCircle L, ‖contRep (by omega) u x‖^6 ∂volume := by
  have hA : Integrable (fun x : AddCircle L =>
      ‖contRep (by omega) u x‖^2 * ‖(weakD u : AddCircle L → ℂ) x‖^2) volume := by
    apply ((Lp.memLp (weightedDerivative u)).integrable_norm_pow' (p := 2)).congr
    filter_upwards [weightedDerivative_ae u] with x hx
    rw [hx, norm_mul, mul_pow]
  have hB : Integrable (fun x : AddCircle L => ‖(densityCandidate u : AddCircle L → ℂ) x‖^2) volume :=
    (Lp.memLp (densityCandidate u)).integrable_norm_pow' (p := 2)
  unfold correction
  rw [quartic_eq, ← integral_norm_sq (densityCandidate u), sexticIntegral_eq,
    integral_add (hA.const_mul 6) hB, integral_const_mul]

/-- REG-008, with `secondExtended` equal to the squared L² second weak
    derivative if it exists and to infinity otherwise. -/
theorem REG008 (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) :
    RealPolynomial (correction (L := L) κ) ∧ Continuous (correction (L := L) κ) ∧
    (∀ u : Hk L 1,
      HasWeakDeriv u.val (weakD u) ∧
      ((densityClass u : AddCircle L → ℂ) =ᵐ[(volume : Measure (AddCircle L))]
        fun x => ((‖contRep (by omega) u x‖^2 : ℝ) : ℂ)) ∧
      HasWeakDeriv (densityClass u) (densityCandidate u) ∧
      ennrealToWithTop (∫⁻ t : ℝ, ENNReal.ofReal (t^4)
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) =
      ennrealToWithTop (secondExtended u) + ↑((κ * (∫ x : AddCircle L,
        6 * (‖contRep (by omega) u x‖^2 * ‖(weakD u : AddCircle L → ℂ) x‖^2) +
        ‖(densityCandidate u : AddCircle L → ℂ) x‖^2 ∂volume) +
        2 * κ^2 * ∫ x : AddCircle L, ‖contRep (by omega) u x‖^6 ∂volume : ℝ))) ∧
    (∀ u : Hk L 1,
      (∫⁻ t : ℝ, ENNReal.ofReal (t^4)
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) ≠ ⊤ ↔
      hsq L 2 (fun n => QuantumNLS.Fourier.coeff L u.val n) ≠ ⊤) ∧
    (∀ (u : Hk L 1) (w : QuantumNLS.PhysicalTensor.L2T L),
      HasWeakDeriv (weakD u) w → secondExtended u = ENNReal.ofReal (‖w‖^2)) ∧
    (∀ u : Hk L 1, (¬ ∃ w, HasWeakDeriv (weakD u) w) → secondExtended u = ⊤) := by
  have hi := extended_fourth_identity L κ hκ
  have he := correction_eq_Rfield (L := L) κ hκ
  refine ⟨?_, continuous_correction κ, ?_, ?_, ?_, ?_⟩
  · rw [he]; exact hi.1
  · intro u
    refine ⟨weakD_is_derivative u, densityClass_ae u, density_product_rule u, ?_⟩
    rw [← correction_printed κ u, he]
    exact hi.2.2.1 u
  · exact (fourth_order_core L κ hκ).2.2.2
  · intro u w hw
    rw [← freeFourth_eq_secondExtended]
    exact freeFourth_eq_norm u hw
  · intro u hw
    rw [← freeFourth_eq_secondExtended]
    exact freeFourth_eq_top u hw

#print axioms correction_printed
#print axioms REG008
end QuantumNLS.TerraMultiRound67REG008
