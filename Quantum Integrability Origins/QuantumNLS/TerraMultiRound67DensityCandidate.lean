import QuantumNLS.TerraMultiRound67Quartic

/-! A continuous L² candidate for the weak derivative of |u|².  The product
    rule identifying this candidate as a weak derivative is a separate goal. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open QuantumNLS.TranslatedCorrelation QuantumNLS.TerraMultiRound67RepMap
open QuantumNLS.TerraMultiRound66WeakMap QuantumNLS.TerraMultiRound67Quartic
open QuantumNLS.RootH1RatioOperator
namespace QuantumNLS.TerraMultiRound67DensityCandidate
variable {L : ℝ} [Fact (0 < L)]

def conjugateWeighted (u : Hk L 1) : Lp ℂ 2 (volume : Measure (AddCircle L)) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure (AddCircle L)) ⊤ 2 2
    (ContinuousMap.toLp (E := ℂ) ⊤ (volume : Measure (AddCircle L)) ℂ (star (repCLM u))) (weakDCLM u)

def densityCandidate (u : Hk L 1) : Lp ℂ 2 (volume : Measure (AddCircle L)) :=
  conjugateWeighted u + Complex.conjCLE.toContinuousLinearMap.compLpL 2 volume (conjugateWeighted u)

theorem continuous_conjugateWeighted : Continuous (conjugateWeighted (L := L)) := by
  unfold conjugateWeighted
  fun_prop

theorem continuous_densityCandidate : Continuous (densityCandidate (L := L)) := by
  unfold densityCandidate
  exact (continuous_conjugateWeighted (L := L)).add
    ((Complex.conjCLE.toContinuousLinearMap.compLpL 2
      (volume : Measure (AddCircle L))).continuous.comp continuous_conjugateWeighted)

theorem densityCandidate_ae (u : Hk L 1) :
    (densityCandidate u : AddCircle L → ℂ) =ᵐ[(volume : Measure (AddCircle L))]
      fun x => conj (contRep (by omega) u x) * (weakD u : AddCircle L → ℂ) x +
        conj ((weakD u : AddCircle L → ℂ) x) * contRep (by omega) u x := by
  have hq : (conjugateWeighted u : AddCircle L → ℂ) =ᵐ[(volume : Measure (AddCircle L))]
      fun x => conj (contRep (by omega) u x) * (weakD u : AddCircle L → ℂ) x := by
    filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
      (ContinuousMap.toLp (E := ℂ) ⊤ (volume : Measure (AddCircle L)) ℂ (star (repCLM u))) (weakDCLM u),
      ContinuousMap.coeFn_toLp (E := ℂ) (p := ⊤) (𝕜 := ℂ)
        (volume : Measure (AddCircle L)) (star (repCLM u))] with x hx hy
    change (conjugateWeighted u : AddCircle L → ℂ) x = _
    rw [show (conjugateWeighted u : AddCircle L → ℂ) x = _ from hx, hy]
    rfl
  filter_upwards [Lp.coeFn_add (conjugateWeighted u)
      (Complex.conjCLE.toContinuousLinearMap.compLpL 2 volume (conjugateWeighted u)),
    Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL (conjugateWeighted u), hq] with x ha hc hq'
  change (conjugateWeighted u + _ : Lp ℂ 2 (volume : Measure (AddCircle L))) x = _
  rw [ha]
  simp only [Pi.add_apply]
  rw [hc, hq']
  change conj (contRep (by omega) u x) * (weakD u : AddCircle L → ℂ) x +
    conj (conj (contRep (by omega) u x) * (weakD u : AddCircle L → ℂ) x) = _
  simp only [map_mul, starRingEnd_self_apply]
  ring

theorem continuous_densityCandidate_sq : Continuous (fun u : Hk L 1 => ‖densityCandidate u‖^2) :=
  (continuous_densityCandidate (L := L)).norm.pow 2

#print axioms continuous_densityCandidate
#print axioms densityCandidate_ae
#print axioms continuous_densityCandidate_sq
end QuantumNLS.TerraMultiRound67DensityCandidate
