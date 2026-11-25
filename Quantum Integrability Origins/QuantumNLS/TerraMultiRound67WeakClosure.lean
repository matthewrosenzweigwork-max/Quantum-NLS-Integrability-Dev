import QuantumNLS.TerraMultiRound67SmoothDense
import QuantumNLS.WeakDerivatives

/-! Weak-derivative identities extend from smooth H¹ fields when both L²
    sides are continuous. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.TranslatedCorrelation QuantumNLS.WeakDerivatives QuantumNLS.Fourier
open QuantumNLS.TerraMultiRound67SmoothDense
namespace QuantumNLS.TerraMultiRound67WeakClosure
variable {L : ℝ} [Fact (0 < L)]

theorem weakDeriv_of_dense_continuous
    (F G : Hk L 1 → Lp ℂ 2 (volume : Measure (AddCircle L)))
    (hF : Continuous F) (hG : Continuous G)
    (hs : ∀ u ∈ smoothFields (L := L), HasWeakDeriv (F u) (G u)) :
    ∀ u, HasWeakDeriv (F u) (G u) := by
  intro u
  apply hasWeakDeriv_of_coeff
  intro n
  let ev : Lp ℂ 2 (volume : Measure (AddCircle L)) → ℂ := fun f => fourierL2 L f n
  have hev : Continuous ev := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous.comp (fourierL2 L).continuous
  have heq : (fun v => ev (G v)) = (fun v => ikn L n * ev (F v)) := by
    apply Continuous.ext_on dense_smoothFields (hev.comp hG) (continuous_const.mul (hev.comp hF))
    intro v hv
    simpa only [ev, fourierL2_apply, Function.comp_apply, Pi.mul_apply] using
      coeff_of_hasWeakDeriv (hs v hv) n
  simpa only [ev, fourierL2_apply] using congrFun heq u

#print axioms weakDeriv_of_dense_continuous
end QuantumNLS.TerraMultiRound67WeakClosure
