import QuantumNLS.TerraMultiRound67DensityCandidate
import QuantumNLS.TerraMultiRound67WeakClosure

/-! Continuous density class and the closure step for its product rule. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open QuantumNLS.TranslatedCorrelation QuantumNLS.WeakDerivatives
open QuantumNLS.TerraMultiRound67RepMap QuantumNLS.TerraMultiRound67DensityCandidate
open QuantumNLS.TerraMultiRound67SmoothDense QuantumNLS.TerraMultiRound67WeakClosure
namespace QuantumNLS.TerraMultiRound67DensityExtension
variable {L : ℝ} [Fact (0 < L)]

def densityClass (u : Hk L 1) : Lp ℂ 2 (volume : Measure (AddCircle L)) :=
  ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ (star (repCLM u) * repCLM u)

theorem continuous_densityClass : Continuous (densityClass (L := L)) := by
  unfold densityClass
  fun_prop

theorem densityClass_ae (u : Hk L 1) :
    (densityClass u : AddCircle L → ℂ) =ᵐ[(volume : Measure (AddCircle L))]
      fun x => ((‖contRep (by omega) u x‖^2 : ℝ) : ℂ) := by
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
      (volume : Measure (AddCircle L)) (star (repCLM u) * repCLM u)] with x hx
  rw [show (densityClass u : AddCircle L → ℂ) x = _ from hx]
  change conj (contRep (by omega) u x) * contRep (by omega) u x = _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

theorem density_product_rule_extension
    (hs : ∀ u ∈ smoothFields (L := L), HasWeakDeriv (densityClass u) (densityCandidate u)) :
    ∀ u : Hk L 1, HasWeakDeriv (densityClass u) (densityCandidate u) :=
  weakDeriv_of_dense_continuous densityClass densityCandidate continuous_densityClass
    continuous_densityCandidate hs

#print axioms densityClass_ae
#print axioms continuous_densityClass
#print axioms density_product_rule_extension
end QuantumNLS.TerraMultiRound67DensityExtension
