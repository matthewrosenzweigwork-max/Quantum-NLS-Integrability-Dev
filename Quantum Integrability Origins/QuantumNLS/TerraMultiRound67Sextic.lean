import QuantumNLS.TerraMultiRound67RepMap
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! Continuity of the sextic part of the printed correction. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open QuantumNLS.TranslatedCorrelation QuantumNLS.TerraMultiRound67RepMap
namespace QuantumNLS.TerraMultiRound67Sextic
variable {L : ℝ} [Fact (0 < L)]

def sexticMap (u : Hk L 1) : C(AddCircle L, ℂ) :=
  star (repCLM u) ^ 3 * (repCLM u) ^ 3

theorem continuous_sexticMap : Continuous (sexticMap (L := L)) := by
  unfold sexticMap
  fun_prop

def sexticIntegral (u : Hk L 1) : ℝ :=
  (∫ x : AddCircle L, sexticMap u x ∂(volume : Measure (AddCircle L))).re

theorem continuous_sexticIntegral : Continuous (sexticIntegral (L := L)) := by
  have hc : Continuous (fun u : Hk L 1 =>
      ContinuousMap.toLp (E := ℂ) 1 (volume : Measure (AddCircle L)) ℂ (sexticMap u)) :=
    (ContinuousMap.toLp (E := ℂ) 1 (volume : Measure (AddCircle L)) ℂ).continuous.comp continuous_sexticMap
  have he (u : Hk L 1) :
      (∫ x : AddCircle L, (ContinuousMap.toLp (E := ℂ) 1
        (volume : Measure (AddCircle L)) ℂ (sexticMap u) : AddCircle L → ℂ) x ∂volume) =
      ∫ x : AddCircle L, sexticMap u x ∂volume := by
    apply integral_congr_ae
    exact ContinuousMap.coeFn_toLp (E := ℂ) (p := 1) (𝕜 := ℂ)
      (volume : Measure (AddCircle L)) (sexticMap u)
  have hh : Continuous (fun u : Hk L 1 =>
      ∫ x : AddCircle L, sexticMap u x ∂(volume : Measure (AddCircle L))) := by
    have hc' := MeasureTheory.continuous_integral.comp hc
    change Continuous (fun u : Hk L 1 => ∫ x : AddCircle L,
      (ContinuousMap.toLp (E := ℂ) 1 (volume : Measure (AddCircle L)) ℂ (sexticMap u) : AddCircle L → ℂ) x ∂volume) at hc'
    simp_rw [he] at hc'
    exact hc'
  exact Complex.continuous_re.comp hh

theorem sexticMap_apply (u : Hk L 1) (x : AddCircle L) :
    sexticMap u x = ((‖contRep (by omega) u x‖^6 : ℝ) : ℂ) := by
  change (conj (contRep (by omega) u x))^3 * (contRep (by omega) u x)^3 = _
  have hz : conj (contRep (by omega) u x) * contRep (by omega) u x =
      ((‖contRep (by omega) u x‖^2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  calc
    _ = (conj (contRep (by omega) u x) * contRep (by omega) u x)^3 := by ring
    _ = _ := by rw [hz]; push_cast; ring

theorem sexticIntegral_eq (u : Hk L 1) : sexticIntegral u =
    ∫ x : AddCircle L, ‖contRep (by omega) u x‖^6 ∂(volume : Measure (AddCircle L)) := by
  unfold sexticIntegral
  change RCLike.re (∫ x : AddCircle L, sexticMap u x ∂(volume : Measure (AddCircle L))) = _
  rw [← integral_re ((sexticMap u).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  filter_upwards with x
  rw [sexticMap_apply]
  exact RCLike.ofReal_re _

#print axioms sexticMap_apply
#print axioms sexticIntegral_eq
#print axioms continuous_sexticMap
#print axioms continuous_sexticIntegral
end QuantumNLS.TerraMultiRound67Sextic
