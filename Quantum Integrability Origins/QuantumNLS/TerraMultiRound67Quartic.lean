import QuantumNLS.TerraMultiRound67RepMap
import QuantumNLS.TerraMultiRound66WeakMap
import QuantumNLS.RootH1RatioOperator
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! Continuity of the |u|²|u'|² term by Hölder multiplication. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.TranslatedCorrelation QuantumNLS.TerraMultiRound67RepMap
open QuantumNLS.TerraMultiRound66WeakMap QuantumNLS.RootH1RatioOperator
namespace QuantumNLS.TerraMultiRound67Quartic
variable {L : ℝ} [Fact (0 < L)]

def weightedDerivative (u : Hk L 1) : Lp ℂ 2 (volume : Measure (AddCircle L)) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure (AddCircle L)) ⊤ 2 2
    (ContinuousMap.toLp (E := ℂ) ⊤ (volume : Measure (AddCircle L)) ℂ (repCLM u)) (weakDCLM u)

theorem continuous_weightedDerivative : Continuous (weightedDerivative (L := L)) := by
  unfold weightedDerivative
  fun_prop

theorem weightedDerivative_ae (u : Hk L 1) :
    (weightedDerivative u : AddCircle L → ℂ) =ᵐ[(volume : Measure (AddCircle L))]
      fun x => contRep (by omega) u x * (weakD u : AddCircle L → ℂ) x := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
      (ContinuousMap.toLp (E := ℂ) ⊤ (volume : Measure (AddCircle L)) ℂ (repCLM u)) (weakDCLM u),
    ContinuousMap.coeFn_toLp (E := ℂ) (p := ⊤) (𝕜 := ℂ)
      (volume : Measure (AddCircle L)) (repCLM u)] with x hx hy
  change (weightedDerivative u : AddCircle L → ℂ) x = _
  rw [show (weightedDerivative u : AddCircle L → ℂ) x = _ from hx, hy]
  rfl

theorem quartic_eq (u : Hk L 1) :
    ‖weightedDerivative u‖^2 =
      ∫ x : AddCircle L, ‖contRep (by omega) u x‖^2 * ‖(weakD u : AddCircle L → ℂ) x‖^2 ∂volume := by
  rw [← integral_norm_sq (weightedDerivative u)]
  apply integral_congr_ae
  filter_upwards [weightedDerivative_ae u] with x hx
  rw [hx, norm_mul, mul_pow]

theorem continuous_quartic : Continuous (fun u : Hk L 1 =>
    ∫ x : AddCircle L, ‖contRep (by omega) u x‖^2 * ‖(weakD u : AddCircle L → ℂ) x‖^2 ∂volume) := by
  have h := (continuous_weightedDerivative (L := L)).norm.pow 2
  change Continuous (fun u : Hk L 1 => ‖weightedDerivative u‖^2) at h
  simp_rw [quartic_eq] at h
  exact h

#print axioms continuous_weightedDerivative
#print axioms weightedDerivative_ae
#print axioms quartic_eq
#print axioms continuous_quartic
end QuantumNLS.TerraMultiRound67Quartic
